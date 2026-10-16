import Zeta23.CCM.OriginalDetectorFourHistorySignedTransfer
import Zeta23.CCM.CanonicalPhysicalTrialRealization
import Zeta23.CCM.CanonicalPoleExponentialMoments

/-!
# The 16κ local-X bound for the original four-history prime forcing

For a continuous pole-neutral test `v` supported in the physical aperture
`[0, L]`, the mixed prime response of the ORIGINAL two-lobe trial obeys

  `‖∫ Prime(f_σ,a) · conj v‖ ≤ 16 κ ‖v‖₂ ‖X‖_{L²[0,L]}`,

where `X` is the actual native prime field and `κ` the fixed original
normalization (`16κ = 8 √(2/n_k)`).

The proof keeps all four signed histories `x-c`, `c-x`, `L-x-c`, `x+c-L`.
It transfers them to `X` through the constructed compact inverse
`g = P⁻¹(conj v)`, which vanishes on `[-L, 0]` because `v` does. It then
applies Cauchy–Schwarz on `[0, L]`, native causality (`X = 0` on
`(-∞, 0]`) for each translated or reflected argument, and the compact
inverse bound `‖g‖₂ ≤ 4‖v‖₂`.

Global `X ∈ L²` is not assumed; only the local norm on `[0, L]` appears.
This bounds the forcing by the native field. It is not the missing
source-specific Step 4 estimate on that field.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- Native causality: the original prime field vanishes on `(-∞, 0]`,
since its first atom enters at `log 2 - s₀ > 0`. -/
theorem nativeOriginalPrimeField_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    nativeOriginalPrimeField t = 0 := by
  show nativePrimeField nativeOriginalSource t = 0
  apply nativePrimeField_zero_before_firstPrime nativeOriginalSource_supported
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hs : UniversalSinc.fixedScale = 1 / 4096 := rfl
  rw [hs]
  linarith

/-- A window `[a, b]` with `a ≤ 0 ≤ b ≤ L` sees no more `X` energy than
`[0, L]`: the part left of zero vanishes by causality. -/
theorem nativeOriginalPrimeField_sq_integral_le {a b L : ℝ}
    (ha : a ≤ 0) (hb0 : 0 ≤ b) (hbL : b ≤ L) :
    (∫ t in a..b, nativeOriginalPrimeField t ^ 2) ≤
      ∫ t in (0 : ℝ)..L, nativeOriginalPrimeField t ^ 2 := by
  have hcont : Continuous fun t => nativeOriginalPrimeField t ^ 2 :=
    nativeOriginalPrimeField_continuous.pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) a 0)
    (hcont.intervalIntegrable (μ := volume) 0 b)
  have hzero : (∫ t in a..0, nativeOriginalPrimeField t ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [uIcc_of_le ha] at ht
      simp [nativeOriginalPrimeField_eq_zero_of_nonpos ht.2]
  rw [← hsplit, hzero, zero_add]
  refine intervalIntegral.integral_mono_interval (μ := volume) le_rfl hb0 hbL ?_
    (hcont.intervalIntegrable _ _)
  exact Filter.Eventually.of_forall fun t => sq_nonneg _

private theorem sq_integral_comp_sub_right_le {L d : ℝ}
    (hd0 : 0 ≤ d) (hdL : d ≤ L) :
    (∫ x in (0 : ℝ)..L, nativeOriginalPrimeField (x - d) ^ 2) ≤
      ∫ t in (0 : ℝ)..L, nativeOriginalPrimeField t ^ 2 := by
  have h := intervalIntegral.integral_comp_sub_right
    (fun t => nativeOriginalPrimeField t ^ 2) (a := 0) (b := L) d
  rw [h]
  exact nativeOriginalPrimeField_sq_integral_le (by linarith) (by linarith)
    (by linarith)

private theorem sq_integral_comp_sub_left_le {L d : ℝ}
    (hd0 : 0 ≤ d) (hdL : d ≤ L) :
    (∫ x in (0 : ℝ)..L, nativeOriginalPrimeField (d - x) ^ 2) ≤
      ∫ t in (0 : ℝ)..L, nativeOriginalPrimeField t ^ 2 := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun t => nativeOriginalPrimeField t ^ 2) (a := 0) (b := L) d
  rw [h]
  exact nativeOriginalPrimeField_sq_integral_le (by linarith) (by linarith)
    (by linarith)

/-- Cauchy–Schwarz on the physical window `[0, L]`. -/
private theorem intervalIntegral_norm_mul_abs_le {L : ℝ} (hL : 0 ≤ L)
    {g : ℝ → ℂ} {h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) :
    (∫ x in (0 : ℝ)..L, ‖g x‖ * |h x|) ≤
      Real.sqrt (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) *
        Real.sqrt (∫ x in (0 : ℝ)..L, h x ^ 2) := by
  rw [intervalIntegral.integral_of_le hL, intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_of_le hL]
  have hgL : MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2)
      (volume.restrict (Ioc (0 : ℝ) L)) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num,
      memLp_two_iff_integrable_sq_norm hg.norm.aestronglyMeasurable]
    exact ((hg.norm.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hhL : MemLp h (ENNReal.ofReal 2) (volume.restrict (Ioc (0 : ℝ) L)) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num,
      memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable]
    exact ((hh.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hCS := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hgL hhL
  simp only [Real.norm_eq_abs, abs_norm, Real.rpow_two, sq_abs] at hCS
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hCS

/-- The constructed compact inverse vanishes left of a source that is
zero on `(-∞, 0]`. -/
theorem nativePoleCompactInverse_eq_zero_of_nonpos {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : ∀ y ≤ 0, f y = 0) {x : ℝ} (hx : x ≤ 0) :
    nativePoleCompactInverse s f x = 0 := by
  have hP : ∀ r : ℝ, nativePolePrimitive s r f x = 0 := by
    intro r
    unfold nativePolePrimitive
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
    · simp
    · intro y hy
      have hy0 : y ≤ 0 := by
        rcases le_total (-s) x with h | h
        · rw [uIcc_of_le h] at hy
          exact hy.2.trans hx
        · rw [uIcc_of_ge h] at hy
          linarith [hy.2]
      simp [hf y hy0]
  unfold nativePoleCompactInverse
  rw [hP, hP]
  ring

/-- A continuous function supported in `[0, L]` vanishes on `(-∞, 0]`,
including the endpoint. -/
private theorem eq_zero_of_nonpos_of_support {v : ℝ → ℂ} (hv : Continuous v)
    {L : ℝ} (hsupp : ∀ x, x ∉ Icc (0 : ℝ) L → v x = 0) {y : ℝ} (hy : y ≤ 0) :
    v y = 0 := by
  have hsub : Iio (0 : ℝ) ⊆ {x | v x = 0} := fun x hx =>
    hsupp x (fun h => absurd h.1 (not_le.mpr hx))
  have hcl : closure (Iio (0 : ℝ)) ⊆ {x | v x = 0} :=
    (isClosed_eq hv continuous_const).closure_subset_iff.mpr hsub
  rw [closure_Iio] at hcl
  exact hcl hy

private theorem eLpNorm_two_toReal_eq_sqrt {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    (eLpNorm g 2 volume).toReal = Real.sqrt (∫ x, ‖g x‖ ^ 2) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg
      (integral_nonneg fun _ => by positivity) _)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]

/-- The four signed history magnitudes on `[0, L]`, for any continuous
weight `g`: Cauchy–Schwarz plus causality for each translated or reflected
argument. Here `L`, `c`, `κ`, `σ` are plain parameters. -/
private theorem fourHistory_weighted_le {L c κ σ : ℝ}
    (hc0 : 0 ≤ c) (hcL : c ≤ L) (hκ : 0 ≤ κ) (hσ : |σ| ≤ 1)
    {g : ℝ → ℂ} (hg : Continuous g) :
    ‖∫ x in (0 : ℝ)..L, g x *
        (((κ * ((nativeOriginalPrimeField (x - c) + nativeOriginalPrimeField (c - x)) +
          σ * (nativeOriginalPrimeField (L - c - x) +
            nativeOriginalPrimeField (x - (L - c))))) : ℝ) : ℂ)‖ ≤
      4 * κ * Real.sqrt (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) *
        Real.sqrt (∫ t in (0 : ℝ)..L, nativeOriginalPrimeField t ^ 2) := by
  have hL : 0 ≤ L := hc0.trans hcL
  have hLc0 : 0 ≤ L - c := by linarith
  have hLcL : L - c ≤ L := by linarith
  have hX : Continuous nativeOriginalPrimeField := nativeOriginalPrimeField_continuous
  have hgn : Continuous fun x => ‖g x‖ := hg.norm
  -- pointwise domination
  have hpt : ∀ x : ℝ, ‖g x *
        (((κ * ((nativeOriginalPrimeField (x - c) + nativeOriginalPrimeField (c - x)) +
          σ * (nativeOriginalPrimeField (L - c - x) +
            nativeOriginalPrimeField (x - (L - c))))) : ℝ) : ℂ)‖ ≤
      κ * (‖g x‖ * |nativeOriginalPrimeField (x - c)| +
        ‖g x‖ * |nativeOriginalPrimeField (c - x)| +
        ‖g x‖ * |nativeOriginalPrimeField (L - c - x)| +
        ‖g x‖ * |nativeOriginalPrimeField (x - (L - c))|) := by
    intro x
    have habs : |(nativeOriginalPrimeField (x - c) + nativeOriginalPrimeField (c - x)) +
          σ * (nativeOriginalPrimeField (L - c - x) +
            nativeOriginalPrimeField (x - (L - c)))| ≤
        |nativeOriginalPrimeField (x - c)| + |nativeOriginalPrimeField (c - x)| +
          |nativeOriginalPrimeField (L - c - x)| +
          |nativeOriginalPrimeField (x - (L - c))| := by
      have h1 := abs_add_le (nativeOriginalPrimeField (x - c))
        (nativeOriginalPrimeField (c - x))
      have h2 := abs_add_le (nativeOriginalPrimeField (L - c - x))
        (nativeOriginalPrimeField (x - (L - c)))
      have h3 := abs_add_le
        (nativeOriginalPrimeField (x - c) + nativeOriginalPrimeField (c - x))
        (σ * (nativeOriginalPrimeField (L - c - x) +
          nativeOriginalPrimeField (x - (L - c))))
      have h4 : |σ * (nativeOriginalPrimeField (L - c - x) +
            nativeOriginalPrimeField (x - (L - c)))| ≤
          |nativeOriginalPrimeField (L - c - x)| +
            |nativeOriginalPrimeField (x - (L - c))| := by
        rw [abs_mul]
        calc |σ| * |nativeOriginalPrimeField (L - c - x) +
              nativeOriginalPrimeField (x - (L - c))|
            ≤ 1 * |nativeOriginalPrimeField (L - c - x) +
              nativeOriginalPrimeField (x - (L - c))| :=
              mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact h2
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hκ]
    calc ‖g x‖ * (κ * |(nativeOriginalPrimeField (x - c) +
            nativeOriginalPrimeField (c - x)) +
          σ * (nativeOriginalPrimeField (L - c - x) +
            nativeOriginalPrimeField (x - (L - c)))|)
        ≤ ‖g x‖ * (κ * (|nativeOriginalPrimeField (x - c)| +
            |nativeOriginalPrimeField (c - x)| +
            |nativeOriginalPrimeField (L - c - x)| +
            |nativeOriginalPrimeField (x - (L - c))|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hκ) (norm_nonneg _)
      _ = _ := by ring
  -- integrability of the four weighted terms
  have hterm : ∀ φ : ℝ → ℝ, Continuous φ →
      IntervalIntegrable (fun x => ‖g x‖ * |nativeOriginalPrimeField (φ x)|) volume 0 L :=
    fun φ hφ => (hgn.mul (hX.comp hφ).abs).intervalIntegrable _ _
  have h1 : IntervalIntegrable
      (fun x => ‖g x‖ * |nativeOriginalPrimeField (x - c)|) volume 0 L :=
    hterm (fun x => x - c) (by fun_prop)
  have h2 : IntervalIntegrable
      (fun x => ‖g x‖ * |nativeOriginalPrimeField (c - x)|) volume 0 L :=
    hterm (fun x => c - x) (by fun_prop)
  have h3 : IntervalIntegrable
      (fun x => ‖g x‖ * |nativeOriginalPrimeField (L - c - x)|) volume 0 L :=
    hterm (fun x => L - c - x) (by fun_prop)
  have h4 : IntervalIntegrable
      (fun x => ‖g x‖ * |nativeOriginalPrimeField (x - (L - c))|) volume 0 L :=
    hterm (fun x => x - (L - c)) (by fun_prop)
  -- Cauchy–Schwarz and causality per history
  have hA0 : 0 ≤ Real.sqrt (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) := Real.sqrt_nonneg _
  have hCS : ∀ φ : ℝ → ℝ, Continuous φ →
      (∫ x in (0 : ℝ)..L, nativeOriginalPrimeField (φ x) ^ 2) ≤
        ∫ t in (0 : ℝ)..L, nativeOriginalPrimeField t ^ 2 →
      (∫ x in (0 : ℝ)..L, ‖g x‖ * |nativeOriginalPrimeField (φ x)|) ≤
        Real.sqrt (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) *
          Real.sqrt (∫ t in (0 : ℝ)..L, nativeOriginalPrimeField t ^ 2) := by
    intro φ hφ hle
    have h : (∫ x in (0 : ℝ)..L, ‖g x‖ * |nativeOriginalPrimeField (φ x)|) ≤
        Real.sqrt (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) *
          Real.sqrt (∫ x in (0 : ℝ)..L, nativeOriginalPrimeField (φ x) ^ 2) :=
      intervalIntegral_norm_mul_abs_le hL hg (hX.comp hφ)
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hA0)
  have hb1 := hCS (fun x => x - c) (by fun_prop) (sq_integral_comp_sub_right_le hc0 hcL)
  have hb2 := hCS (fun x => c - x) (by fun_prop) (sq_integral_comp_sub_left_le hc0 hcL)
  have hb3 := hCS (fun x => L - c - x) (by fun_prop)
    (sq_integral_comp_sub_left_le hLc0 hLcL)
  have hb4 := hCS (fun x => x - (L - c)) (by fun_prop)
    (sq_integral_comp_sub_right_le hLc0 hLcL)
  have hsum : (∫ x in (0 : ℝ)..L,
        κ * (‖g x‖ * |nativeOriginalPrimeField (x - c)| +
          ‖g x‖ * |nativeOriginalPrimeField (c - x)| +
          ‖g x‖ * |nativeOriginalPrimeField (L - c - x)| +
          ‖g x‖ * |nativeOriginalPrimeField (x - (L - c))|)) =
      κ * ((∫ x in (0 : ℝ)..L, ‖g x‖ * |nativeOriginalPrimeField (x - c)|) +
        (∫ x in (0 : ℝ)..L, ‖g x‖ * |nativeOriginalPrimeField (c - x)|) +
        (∫ x in (0 : ℝ)..L, ‖g x‖ * |nativeOriginalPrimeField (L - c - x)|) +
        (∫ x in (0 : ℝ)..L, ‖g x‖ * |nativeOriginalPrimeField (x - (L - c))|)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((h1.add h2).add h3) h4,
      intervalIntegral.integral_add (h1.add h2) h3,
      intervalIntegral.integral_add h1 h2]
  have hcont_full : Continuous fun x => g x *
      (((κ * ((nativeOriginalPrimeField (x - c) + nativeOriginalPrimeField (c - x)) +
        σ * (nativeOriginalPrimeField (L - c - x) +
          nativeOriginalPrimeField (x - (L - c))))) : ℝ) : ℂ) := by
    fun_prop
  calc ‖∫ x in (0 : ℝ)..L, g x *
        (((κ * ((nativeOriginalPrimeField (x - c) + nativeOriginalPrimeField (c - x)) +
          σ * (nativeOriginalPrimeField (L - c - x) +
            nativeOriginalPrimeField (x - (L - c))))) : ℝ) : ℂ)‖
      ≤ ∫ x in (0 : ℝ)..L, ‖g x *
        (((κ * ((nativeOriginalPrimeField (x - c) + nativeOriginalPrimeField (c - x)) +
          σ * (nativeOriginalPrimeField (L - c - x) +
            nativeOriginalPrimeField (x - (L - c))))) : ℝ) : ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hL
    _ ≤ ∫ x in (0 : ℝ)..L,
        κ * (‖g x‖ * |nativeOriginalPrimeField (x - c)| +
          ‖g x‖ * |nativeOriginalPrimeField (c - x)| +
          ‖g x‖ * |nativeOriginalPrimeField (L - c - x)| +
          ‖g x‖ * |nativeOriginalPrimeField (x - (L - c))|) := by
        apply intervalIntegral.integral_mono_on hL
        · exact hcont_full.norm.intervalIntegrable _ _
        · exact (((h1.add h2).add h3).add h4).const_mul κ
        · intro x _
          exact hpt x
    _ = _ := hsum
    _ ≤ κ * (4 * (Real.sqrt (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) *
          Real.sqrt (∫ t in (0 : ℝ)..L, nativeOriginalPrimeField t ^ 2))) :=
        mul_le_mul_of_nonneg_left (by linarith [hb1, hb2, hb3, hb4]) hκ
    _ = _ := by ring

/-- **16κ local-X bound.** The original trial's mixed prime response
against a continuous pole-neutral test supported in `[0, L]` is controlled
by the local `L²[0, L]` norm of the actual native prime field. All four
signed histories are kept; no global `X ∈ L²` is assumed. -/
theorem originalDetector_primeResponse_pairing_le_sixteenKappa
    {σ a : ℝ} (hσ : |σ| ≤ 1) (ha : 0 ≤ a)
    {v : ℝ → ℂ} (hv : Continuous v)
    (hvsupp : ∀ x, x ∉ Icc (0 : ℝ) (fixedOriginalSincTrialAperture a) → v x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * v x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * v x) = 0) :
    ‖∫ x : ℝ, nativeWeilPrimeResponse (fixedOriginalSincPhaseTrial σ a) x *
        conj (v x)‖ ≤
      16 * fixedOriginalSincTrialNormalization * (eLpNorm v 2 volume).toReal *
        Real.sqrt (∫ t in (0 : ℝ)..fixedOriginalSincTrialAperture a,
          nativeOriginalPrimeField t ^ 2) := by
  -- Geometry of the fixed original trial.
  have hc0 : 0 ≤ fixedOriginalSincLobeCenter := by
    have hs : UniversalSinc.fixedScale = 1 / 4096 := rfl
    rw [show fixedOriginalSincLobeCenter = 1 + UniversalSinc.fixedScale from rfl, hs]
    norm_num
  have hcL : fixedOriginalSincLobeCenter ≤ fixedOriginalSincTrialAperture a := by
    simp only [fixedOriginalSincTrialAperture]
    linarith
  have hL : 0 ≤ fixedOriginalSincTrialAperture a := hc0.trans hcL
  have hκ : 0 ≤ fixedOriginalSincTrialNormalization := by
    simp only [fixedOriginalSincTrialNormalization]
    positivity
  -- The conjugated test is a legitimate compact pole-neutral source.
  let f : ℝ → ℂ := fun x => conj (v x)
  have hfc : Continuous f := Complex.continuous_conj.comp hv
  have hvzero : ∀ y ≤ 0, v y = 0 := fun y hy =>
    eq_zero_of_nonpos_of_support hv hvsupp hy
  have hfzero : ∀ y ≤ 0, f y = 0 := fun y hy => by
    simp [f, hvzero y hy]
  have hfcs : HasCompactSupport f :=
    HasCompactSupport.intro (K := Icc (0 : ℝ) (fixedOriginalSincTrialAperture a))
      isCompact_Icc fun x hx => by simp [f, hvsupp x hx]
  have hfL2 : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfcs
  have hfsupp : ∀ x, x ∉ Icc (-fixedOriginalSincTrialAperture a)
      (fixedOriginalSincTrialAperture a) → f x = 0 := by
    intro x hx
    have hx' : x ∉ Icc (0 : ℝ) (fixedOriginalSincTrialAperture a) := fun h =>
      hx ⟨by linarith [h.1], h.2⟩
    simp [f, hvsupp x hx']
  have hconj : ∀ r : ℝ, (∫ x : ℝ, nativePoleExponential r x * f x) =
      conj (∫ x : ℝ, nativePoleExponential r x * v x) := by
    intro r
    rw [← integral_conj]
    congr 1
    funext x
    show (Real.exp (r * x) : ℂ) * conj (v x) = conj ((Real.exp (r * x) : ℂ) * v x)
    rw [map_mul, Complex.conj_ofReal]
  have hfplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0 := by
    rw [hconj, hplus, map_zero]
  have hfminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0 := by
    rw [hconj, hminus, map_zero]
  have hu0 : ∀ x ≤ 0,
      (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x = 0 := fun x hx =>
    nativePoleCompactInverse_eq_zero_of_nonpos hL hfzero hx
  -- Global prime pairing equals the signed four-history interval pairing.
  have hglob : (∫ x : ℝ, nativeWeilPrimeResponse (fixedOriginalSincPhaseTrial σ a) x *
        conj (v x)) =
      ∫ x in (-fixedOriginalSincTrialAperture a)..(fixedOriginalSincTrialAperture a),
        f x * originalSmoothFourPrimeHistories σ a x := by
    have hcompl : ∀ x, x ∉ Icc (-fixedOriginalSincTrialAperture a)
        (fixedOriginalSincTrialAperture a) →
        f x * originalSmoothFourPrimeHistories σ a x = 0 := fun x hx => by
      rw [hfsupp x hx, zero_mul]
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    congr 1
    funext x
    rw [originalSmoothFourPrimeHistories_eq, mul_comm]
  -- Transfer to the actual native field, then drop the vanishing left half.
  have htransfer := (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus
    ).originalSmoothFourPrimeHistories_to_actualX hfc σ a
  have hXc : Continuous fun x : ℝ => originalSmoothFourPrimeXHistories σ a x := by
    unfold originalSmoothFourPrimeXHistories
    have hX := nativeOriginalPrimeField_continuous
    fun_prop
  have hint : ∀ p q : ℝ, IntervalIntegrable
      (fun x => (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x *
        originalSmoothFourPrimeXHistories σ a x) volume p q :=
    fun p q => ((nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value_continuous.mul
      hXc).intervalIntegrable p q
  have hhalf : (∫ x in (-fixedOriginalSincTrialAperture a)..(fixedOriginalSincTrialAperture a),
        (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x *
          originalSmoothFourPrimeXHistories σ a x) =
      ∫ x in (0 : ℝ)..(fixedOriginalSincTrialAperture a),
        (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x *
          originalSmoothFourPrimeXHistories σ a x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint (-fixedOriginalSincTrialAperture a) 0)
      (hint 0 (fixedOriginalSincTrialAperture a))]
    have hleft : (∫ x in (-fixedOriginalSincTrialAperture a)..0,
        (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x *
          originalSmoothFourPrimeXHistories σ a x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
      · simp
      · intro x hx
        rw [uIcc_of_le (by linarith)] at hx
        simp [hu0 x hx.2]
    rw [hleft, zero_add]
  -- Rewrite the four X histories as one real-valued signed combination.
  have hreal : (∫ x in (0 : ℝ)..(fixedOriginalSincTrialAperture a),
        (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x *
          originalSmoothFourPrimeXHistories σ a x) =
      ∫ x in (0 : ℝ)..(fixedOriginalSincTrialAperture a),
        (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x *
          (((fixedOriginalSincTrialNormalization *
            ((nativeOriginalPrimeField (x - fixedOriginalSincLobeCenter) +
              nativeOriginalPrimeField (fixedOriginalSincLobeCenter - x)) +
            σ * (nativeOriginalPrimeField
                (fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter - x) +
              nativeOriginalPrimeField
                (x - (fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter))))) :
              ℝ) : ℂ) := by
    congr 1
    funext x
    congr 1
    unfold originalSmoothFourPrimeXHistories
    rw [show fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter =
        fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter - x by ring,
      show x + fixedOriginalSincLobeCenter - fixedOriginalSincTrialAperture a =
        x - (fixedOriginalSincTrialAperture a - fixedOriginalSincLobeCenter) by ring]
    push_cast
    ring
  rw [hglob, htransfer, hhalf, hreal]
  -- Cauchy–Schwarz/causality, then the compact-inverse estimate.
  have hmain := fourHistory_weighted_le hc0 hcL hκ hσ
    (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value_continuous
  have huL2 : MemLp (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value 2 volume :=
    (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value_l2
  have hAle : Real.sqrt (∫ x in (0 : ℝ)..(fixedOriginalSincTrialAperture a),
        ‖(nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x‖ ^ 2) ≤
      (eLpNorm (nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value 2 volume).toReal := by
    rw [eLpNorm_two_toReal_eq_sqrt huL2]
    apply Real.sqrt_le_sqrt
    rw [intervalIntegral.integral_of_le hL]
    exact setIntegral_le_integral
      ((memLp_two_iff_integrable_sq_norm huL2.1).mp huL2)
      (Filter.Eventually.of_forall fun _ => by positivity)
  have hnorm := nativePoleCompactH2_norm_bound hL hfL2 hfsupp hfplus hfminus
  have hfv : eLpNorm f 2 volume = eLpNorm v 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp [f])
  rw [hfv] at hnorm
  have hB0 : 0 ≤ Real.sqrt (∫ t in (0 : ℝ)..fixedOriginalSincTrialAperture a,
      nativeOriginalPrimeField t ^ 2) := Real.sqrt_nonneg _
  refine hmain.trans ?_
  calc 4 * fixedOriginalSincTrialNormalization *
        Real.sqrt (∫ x in (0 : ℝ)..(fixedOriginalSincTrialAperture a),
          ‖(nativePoleCompactH2 hL hfL2 hfsupp hfplus hfminus).value x‖ ^ 2) *
        Real.sqrt (∫ t in (0 : ℝ)..fixedOriginalSincTrialAperture a,
          nativeOriginalPrimeField t ^ 2)
      ≤ 4 * fixedOriginalSincTrialNormalization *
          (4 * (eLpNorm v 2 volume).toReal) *
        Real.sqrt (∫ t in (0 : ℝ)..fixedOriginalSincTrialAperture a,
          nativeOriginalPrimeField t ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hAle.trans hnorm) (by linarith)) hB0
    _ = _ := by ring

/-- Every actual native pole-neutral finite vector synthesizes a physical
test with both elementary-pole moments equal to zero. -/
theorem canonicalNativePhysicalSynthesis_poleMoments (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (v : nativePoleNeutralParitySpace σ L K) :
    (∫ x : ℝ, nativePoleExponential (1 / 2) x *
        finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v) x) = 0 ∧
    (∫ x : ℝ, nativePoleExponential (-1 / 2) x *
        finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v) x) = 0 := by
  have hm : canonicalPoleExponentialMoment 1 L K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (canonicalNativeCoefficientInclusion σ L K v)) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (canonicalNativeCoefficientInclusion σ L K v)) = 0 := by
    cases σ
    · exact (poleNeutralEven_iff_exponentialMoments hL K v.val).mp v.property
    · exact (poleNeutralOdd_iff_exponentialMoments hL K v.val).mp v.property
  constructor
  · refine Eq.trans ?_ hm.1
    unfold canonicalPoleExponentialMoment
    congr 1
    funext x
    unfold nativePoleExponential
    rw [show (1 / 2 : ℝ) * x = 1 * x / 2 by ring]
    rfl
  · refine Eq.trans ?_ hm.2
    unfold canonicalPoleExponentialMoment
    congr 1
    funext x
    unfold nativePoleExponential
    rw [show (-1 / 2 : ℝ) * x = -1 * x / 2 by ring]
    rfl

/-- **16κ bound on the actual native predecessor tests.** For every finite
pole-neutral vector `v` of either parity at the original aperture, the
prime part of the original trial's projected forcing against its physical
synthesis is at most `16 κ ‖v‖ ‖X‖_{L²[0,L]}`. The test is the literal
physical realization used by the detector Schur state; nothing is assumed
about it beyond membership in the native carrier. -/
theorem originalDetector_nativeTest_primeForcing_le_sixteenKappa
    (σ : ReversalParity) {τ a : ℝ} (hτ : |τ| ≤ 1) (ha : 0 ≤ a) (K : ℕ)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a) K) :
    ‖∫ x : ℝ, nativeWeilPrimeResponse (fixedOriginalSincPhaseTrial τ a) x *
        conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a) K
          (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) K v) x)‖ ≤
      16 * fixedOriginalSincTrialNormalization * ‖v‖ *
        Real.sqrt (∫ t in (0 : ℝ)..fixedOriginalSincTrialAperture a,
          nativeOriginalPrimeField t ^ 2) := by
  have hL : 0 < fixedOriginalSincTrialAperture a := by
    have hs : UniversalSinc.fixedScale = 1 / 4096 := rfl
    rw [show fixedOriginalSincTrialAperture a =
        2 * a + 2 * (1 + UniversalSinc.fixedScale) from rfl, hs]
    linarith
  have hlegal : canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) K v ∈
      euclideanBoundaryFlatSubspace K := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ _ K v
  have hcont : Continuous (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a) K
      (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) K v)) :=
    (contDiff_localizedFiniteVector_of_boundaryFlat K _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K _).mp hlegal)).continuous
  have hsupp : ∀ x, x ∉ Icc (0 : ℝ) (fixedOriginalSincTrialAperture a) →
      finitePhysicalSynthesis (fixedOriginalSincTrialAperture a) K
        (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) K v) x = 0 := by
    intro x hx
    simp [finitePhysicalSynthesis, localizedFiniteVector, localizedZeroExtendedMode,
      Set.indicator_of_notMem hx]
  have hmom := canonicalNativePhysicalSynthesis_poleMoments σ hL K v
  have hbound := originalDetector_primeResponse_pairing_le_sixteenKappa hτ ha hcont hsupp
    hmom.1 hmom.2
  have hwL2 : MemLp (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a) K
      (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) K v)) 2 volume :=
    localizedFiniteVector_memLp_two _ K _
  have hnorm : (eLpNorm (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a) K
      (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) K v))
        2 volume).toReal = ‖v‖ := by
    rw [eLpNorm_two_toReal_eq_sqrt hwL2, finitePhysicalSynthesis_energy hL K,
      Real.sqrt_sq (norm_nonneg _), LinearIsometry.norm_map]
  rw [hnorm] at hbound
  exact hbound

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalPrimeField_eq_zero_of_nonpos
#print axioms Zeta23.CCM.nativeOriginalPrimeField_sq_integral_le
#print axioms Zeta23.CCM.nativePoleCompactInverse_eq_zero_of_nonpos
#print axioms Zeta23.CCM.originalDetector_primeResponse_pairing_le_sixteenKappa
#print axioms Zeta23.CCM.canonicalNativePhysicalSynthesis_poleMoments
#print axioms Zeta23.CCM.originalDetector_nativeTest_primeForcing_le_sixteenKappa
