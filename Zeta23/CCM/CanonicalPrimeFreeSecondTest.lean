import Zeta23.CCM.CanonicalSourceWeightedIntegral
import Zeta23.CCM.SourceFourierConvolution
import Zeta23.CCM.DictionaryCompletePhysicalRHS
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284 follow-up M42 (Steps 79, 101–102): explicit prime-free positivity radius

For a centered coefficient vector `z` put `e(ω) = Re e_{Dz}(ω)` (`(Dz)_n = n z_n`)
and define the fixed-vector prime-free physical second-order test

`Q_K(L, z) = ∫₀ᴸ t² (W(t) - ρ(t)) e(1 - t/L) dt`,

`W(t) = e^{-t/2} + e^{t/2}` (`completeSourcePoleWeight`), `ρ = archDensity`.
For `0 < L < log 2` there are no prime samples, so this is the handoff's
`𝒜_L[t² e_{Dz}(1 - t/L)]`.

Proved here:

* `|S_nm(ω)| ≤ 2ω` for `ω ≥ 0` (from the exact cosine-integral form) and
  `|e_{Dz}(ω)| ≤ 2ω (2K+1) K² ‖z‖²`;
* `|t²(W(t) - ρ(t)) + t/2| ≤ 3t²` for `0 < t ≤ log 2`;
* for `∑ z = 0`, `0 < L ≤ log 2`:
  `Q_K(L, z) ≥ L² ‖z‖² [1/(4π²) - L(2K+1)K²/2]` (uses the compiled weighted
  source identity `∫₀¹ (1-ω) e = -‖z‖²/(2π²)`);
* hence `Q_K(L, z) > 0` for `z ≠ 0` and `0 < L < 1/(2π²(2K+1)K²)`.

Scope: this is a statement about the fixed-vector test functional.  Its
identification with the actual aperture derivative `E'' + (2/L) E'` of the
canonical energy (prime-free F04, M65) is OPEN, as is any contact exclusion.
-/

/-! ## Source bounds -/

/-- `|S_nm(ω)| ≤ 2ω` for `ω ≥ 0`. -/
theorem norm_sourceEntry_le {ω : ℝ} (hω : 0 ≤ ω) (n m : ℤ) :
    ‖sourceEntry ω n m‖ ≤ 2 * ω := by
  rw [sourceEntry_eq_cos_integral, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hpi := Real.pi_pos
  have hint : |∫ t in (0 : ℝ)..(2 * Real.pi * ω),
      Real.cos ((n : ℝ) * t + (m : ℝ) * (2 * Real.pi * ω - t))| ≤ 1 * |2 * Real.pi * ω - 0| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 2 * Real.pi * ω) (C := 1)
      (f := fun t => Real.cos ((n : ℝ) * t + (m : ℝ) * (2 * Real.pi * ω - t)))
      (fun t _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    simpa [Real.norm_eq_abs] using this
  rw [sub_zero, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * ω), one_mul] at hint
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  calc 1 / Real.pi * |∫ t in (0 : ℝ)..(2 * Real.pi * ω),
        Real.cos ((n : ℝ) * t + (m : ℝ) * (2 * Real.pi * ω - t))| ≤
        1 / Real.pi * (2 * Real.pi * ω) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 2 * ω := by field_simp

/-- `|e_u(ω)| ≤ 2ω (∑ |u_i|)²` for `ω ≥ 0`. -/
theorem norm_quadraticForm_sourceMatrix_le {ω : ℝ} (hω : 0 ≤ ω) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    ‖quadraticForm (sourceMatrix ω N) u‖ ≤ 2 * ω * (∑ i, ‖u i‖) ^ 2 := by
  unfold quadraticForm
  calc ‖∑ i, ∑ j, conj (u i) * sourceMatrix ω N i j * u j‖ ≤
        ∑ i, ∑ j, ‖conj (u i) * sourceMatrix ω N i j * u j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, ‖u i‖ * (2 * ω) * ‖u j‖ := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [norm_mul, norm_mul, Complex.norm_conj, sourceMatrix_apply]
        have := norm_sourceEntry_le hω (centeredIndex N i) (centeredIndex N j)
        gcongr
    _ = 2 * ω * (∑ i, ‖u i‖) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring

/-- `|Re e_{Dz}(ω)| ≤ 2ω (2N+1) N² ‖z‖²` for `ω ≥ 0`. -/
theorem abs_re_quadraticForm_index_le {ω : ℝ} (hω : 0 ≤ ω) (N : ℕ)
    (z : Fin (2 * N + 1) → ℂ) :
    |(quadraticForm (sourceMatrix ω N) (indexMatrix N *ᵥ z)).re| ≤
      2 * ω * (2 * N + 1) * N ^ 2 * ∑ i, Complex.normSq (z i) := by
  set u := indexMatrix N *ᵥ z with hu
  have hui : ∀ i, ‖u i‖ ≤ N * ‖z i‖ := by
    intro i
    have : u i = ((centeredIndex N i : ℤ) : ℂ) * z i := by
      simp [hu, indexMatrix, Matrix.mulVec_diagonal]
    rw [this, norm_mul, Complex.norm_intCast]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h1 := i.2
    have habs : |centeredIndex N i| ≤ (N : ℤ) := by
      rw [abs_le]; simp only [centeredIndex]; omega
    have : |((centeredIndex N i : ℤ) : ℝ)| ≤ (N : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast habs
    exact this
  have hcs : (∑ i, ‖u i‖) ^ 2 ≤ ((2 * N + 1 : ℕ) : ℝ) * ∑ i, ‖u i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (2 * N + 1))))
      (f := fun i => ‖u i‖)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hsq : ∑ i, ‖u i‖ ^ 2 ≤ (N : ℝ) ^ 2 * ∑ i, Complex.normSq (z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Complex.normSq_eq_norm_sq]
    have := hui i
    have h0 := norm_nonneg (u i)
    nlinarith [norm_nonneg (z i)]
  have hnorm := norm_quadraticForm_sourceMatrix_le hω N u
  calc |(quadraticForm (sourceMatrix ω N) u).re| ≤ ‖quadraticForm (sourceMatrix ω N) u‖ :=
        Complex.abs_re_le_norm _
    _ ≤ 2 * ω * (∑ i, ‖u i‖) ^ 2 := hnorm
    _ ≤ 2 * ω * (((2 * N + 1 : ℕ) : ℝ) * ((N : ℝ) ^ 2 * ∑ i, Complex.normSq (z i))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hcs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = 2 * ω * (2 * N + 1) * N ^ 2 * ∑ i, Complex.normSq (z i) := by
        push_cast; ring

/-! ## The prime-free kernel -/

/-- Prime-free physical weight `W - ρ`. -/
def primeFreeKernel (t : ℝ) : ℝ := completeSourcePoleWeight t - archDensity t

/-- `|t²(W(t) - ρ(t)) + t/2| ≤ 3t²` on `0 < t ≤ log 2`. -/
theorem abs_sq_mul_primeFreeKernel_add_le {t : ℝ} (ht : 0 < t) (ht2 : t ≤ Real.log 2) :
    |t ^ 2 * primeFreeKernel t + t / 2| ≤ 3 * t ^ 2 := by
  set y := Real.exp (t / 2) with hy
  have hy1 : 1 < y := by
    have := Real.add_one_lt_exp (x := t / 2) (by positivity)
    linarith
  have hyy : y ^ 2 = Real.exp t := by
    rw [hy, sq, ← Real.exp_add]; ring_nf
  have hexp_le : Real.exp t ≤ 2 := by
    calc Real.exp t ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr ht2
      _ = 2 := Real.exp_log (by norm_num)
  have hy2 : y ^ 2 ≤ 2 := hyy ▸ hexp_le
  have hneg : Real.exp (-t) = 1 / y ^ 2 := by
    rw [hyy, Real.exp_neg, one_div]
  have hneghalf : Real.exp (-t / 2) = 1 / y := by
    rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg, one_div]
  have hlog : Real.log y = t / 2 := by rw [hy, Real.log_exp]
  have hlogle : 1 - y⁻¹ ≤ t / 2 := hlog ▸ Real.one_sub_inv_le_log_of_pos (by linarith)
  have hsinh : 2 * t ≤ Real.exp t - Real.exp (-t) := by
    have h := Real.self_le_sinh_iff.mpr ht.le
    rw [Real.sinh_eq] at h
    linarith
  have hexpm : y - 1 ≤ t / 2 * y := by
    have h := Real.add_one_le_exp (-(t / 2))
    rw [Real.exp_neg] at h
    have hy0 : 0 < y := by linarith
    have : (-(t / 2) + 1) * y ≤ y⁻¹ * y := mul_le_mul_of_nonneg_right h hy0.le
    rw [inv_mul_cancel₀ hy0.ne'] at this
    nlinarith
  have hy0 : 0 < y := by linarith
  have hD : Real.exp t - Real.exp (-t) = y ^ 2 - 1 / y ^ 2 := by rw [hneg, hyy]
  have hDpos : 0 < y ^ 2 - 1 / y ^ 2 := by rw [← hD]; linarith
  have hρ : archDensity t = y / (y ^ 2 - 1 / y ^ 2) := by
    unfold archDensity; rw [← hD]
  have hW : completeSourcePoleWeight t = 1 / y + y := by
    unfold completeSourcePoleWeight; rw [hneghalf]
  have hyle : y ≤ 3 / 2 := by nlinarith
  -- polynomial core: `y² - y⁻² ≤ 4 (y - 1)` on `1 ≤ y`, `y² ≤ 2`
  have hpoly : y ^ 2 - 1 / y ^ 2 ≤ 4 * (y - 1) := by
    have e : y ^ 2 - 1 / y ^ 2 = (y ^ 4 - 1) / y ^ 2 := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have hq : 0 ≤ -(y ^ 2 - 2 * y - 1) := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (y - 1)) hq]
  have h2ty : 4 * (y - 1) ≤ 2 * t * y := by
    have := mul_le_mul_of_nonneg_left hlogle (by linarith : (0 : ℝ) ≤ 4 * y)
    rw [mul_sub, mul_one, mul_assoc, mul_inv_cancel₀ hy0.ne', mul_one] at this
    nlinarith
  -- `1/2 ≤ t ρ(t) ≤ y/2`
  have hr_low : 1 / 2 ≤ t * archDensity t := by
    rw [hρ, mul_div_assoc', le_div_iff₀ hDpos]
    nlinarith
  have hr_high : t * archDensity t ≤ y / 2 := by
    rw [hρ, mul_div_assoc', div_le_iff₀ hDpos]
    have : 2 * t ≤ y ^ 2 - 1 / y ^ 2 := by rw [← hD]; exact hsinh
    nlinarith
  have hW3 : completeSourcePoleWeight t ≤ 3 := by
    rw [hW]
    have : 1 / y ≤ 1 := by rw [div_le_one hy0]; linarith
    linarith
  have hW0 : 0 ≤ completeSourcePoleWeight t := by
    rw [hW]; positivity
  have e : t ^ 2 * primeFreeKernel t + t / 2 =
      t * (t * completeSourcePoleWeight t - t * archDensity t + 1 / 2) := by
    unfold primeFreeKernel; ring
  rw [e, abs_le]
  constructor
  · have : -3 * t ≤ t * completeSourcePoleWeight t - t * archDensity t + 1 / 2 := by
      nlinarith
    nlinarith
  · have : t * completeSourcePoleWeight t - t * archDensity t + 1 / 2 ≤ 3 * t := by
      nlinarith
    nlinarith

/-! ## The prime-free test and its lower bound -/

/-- The fixed-vector prime-free second-order physical test
`Q_N(L, z) = ∫₀ᴸ t² (W - ρ)(t) Re e_{Dz}(1 - t/L) dt`. -/
def primeFreeSecondTest (N : ℕ) (z : Fin (2 * N + 1) → ℂ) (L : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L,
    t ^ 2 * primeFreeKernel t *
      (quadraticForm (sourceMatrix (1 - t / L) N) (indexMatrix N *ᵥ z)).re

private theorem measurable_primeFreeKernel : Measurable primeFreeKernel := by
  unfold primeFreeKernel completeSourcePoleWeight archDensity
  fun_prop

/-- `∫₀ᴸ (t/2) e_{Dz}(1 - t/L) dt = -L² ‖z‖² / (4π²)` for `∑ z = 0`. -/
theorem integral_half_mul_re_energy_index (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hsum : ∑ i, z i = 0) {L : ℝ} (hL : 0 < L) :
    ∫ t in (0 : ℝ)..L, t / 2 *
        (quadraticForm (sourceMatrix (1 - t / L) N) (indexMatrix N *ᵥ z)).re =
      -(L ^ 2 / (4 * Real.pi ^ 2)) * ∑ i, Complex.normSq (z i) := by
  set e : ℝ → ℝ := fun ω => (quadraticForm (sourceMatrix ω N) (indexMatrix N *ᵥ z)).re
    with he
  have hcv := intervalIntegral.integral_comp_div (a := 0) (b := L)
    (f := fun x => L * x / 2 * e (1 - x)) hL.ne'
  simp only [zero_div, div_self hL.ne', smul_eq_mul] at hcv
  have h1 : ∫ t in (0 : ℝ)..L, t / 2 * e (1 - t / L) =
      ∫ x in (0 : ℝ)..L, L * (x / L) / 2 * e (1 - x / L) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    congr 1
    field_simp
  have hsl := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (f := fun ω => L * (1 - ω) / 2 * e ω) 1
  simp only [sub_self, sub_zero, sub_sub_cancel] at hsl
  have h3 : ∫ ω in (0 : ℝ)..1, L * (1 - ω) / 2 * e ω =
      L / 2 * ∫ ω in (0 : ℝ)..1, (1 - ω) * e ω := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ω _
    simp only
    ring
  change ∫ t in (0 : ℝ)..L, t / 2 * e (1 - t / L) = _
  rw [h1, hcv, hsl, h3]
  have hint := integral_one_sub_mul_re_energy_indexAction N z hsum
  rw [he]
  simp only at hint ⊢
  rw [hint]
  ring

/-- `∫₀ᴸ t² (1 - t/L) dt = L³/12`. -/
theorem integral_sq_mul_one_sub_div {L : ℝ} (hL : 0 < L) :
    ∫ t in (0 : ℝ)..L, t ^ 2 * (1 - t / L) = L ^ 3 / 12 := by
  have h : ∫ t in (0 : ℝ)..L, t ^ 2 * (1 - t / L) =
      ∫ t in (0 : ℝ)..L, (t ^ 2 - (1 / L) * t ^ 3) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    field_simp
  rw [h, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable 0 L)
      ((by fun_prop : Continuous fun t : ℝ => (1 / L) * t ^ 3).intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  field_simp
  ring

/-- **M42 explicit lower bound.**  For `∑ z = 0` and `0 < L ≤ log 2`,
`Q_N(L, z) ≥ L² ‖z‖² [1/(4π²) - L(2N+1)N²/2]`. -/
theorem primeFreeSecondTest_ge (N : ℕ) (z : Fin (2 * N + 1) → ℂ) (hsum : ∑ i, z i = 0)
    {L : ℝ} (hL : 0 < L) (hL2 : L ≤ Real.log 2) :
    L ^ 2 * (∑ i, Complex.normSq (z i)) *
        (1 / (4 * Real.pi ^ 2) - L * (2 * N + 1) * N ^ 2 / 2) ≤
      primeFreeSecondTest N z L := by
  set M := ∑ i, Complex.normSq (z i) with hM
  set e : ℝ → ℝ := fun ω => (quadraticForm (sourceMatrix ω N) (indexMatrix N *ᵥ z)).re
    with he
  set C : ℝ := 2 * (2 * N + 1) * N ^ 2 * M with hC
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hC0 : 0 ≤ C := by positivity
  have hecont : Continuous e :=
    Complex.continuous_re.comp (continuous_quadraticForm_sourceMatrix N _)
  have hcomp : Continuous fun t : ℝ => e (1 - t / L) :=
    hecont.comp (continuous_const.sub (continuous_id.div_const L))
  have hebound : ∀ t ∈ Set.Icc (0 : ℝ) L, |e (1 - t / L)| ≤ (1 - t / L) * C := by
    intro t ht
    have hω : 0 ≤ 1 - t / L := by
      rw [sub_nonneg, div_le_one hL]; exact ht.2
    have := abs_re_quadraticForm_index_le hω N z
    rw [he]
    simp only
    calc _ ≤ 2 * (1 - t / L) * (2 * N + 1) * N ^ 2 * M := this
      _ = (1 - t / L) * C := by rw [hC]; ring
  set f : ℝ → ℝ := fun t => t ^ 2 * primeFreeKernel t * e (1 - t / L) with hf
  set g : ℝ → ℝ := fun t => -(t / 2 * e (1 - t / L)) - 3 * C * (t ^ 2 * (1 - t / L)) with hg
  have hfg : ∀ t ∈ Set.Icc (0 : ℝ) L, g t ≤ f t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0; simp [hf, hg]
    have hk := abs_sq_mul_primeFreeKernel_add_le hpos (ht.2.trans hL2)
    have hb := hebound t ht
    have hab : -(|t ^ 2 * primeFreeKernel t + t / 2| * |e (1 - t / L)|) ≤
        (t ^ 2 * primeFreeKernel t + t / 2) * e (1 - t / L) := by
      rw [← abs_mul]; exact neg_abs_le _
    have hprod : |t ^ 2 * primeFreeKernel t + t / 2| * |e (1 - t / L)| ≤
        3 * t ^ 2 * ((1 - t / L) * C) :=
      mul_le_mul hk hb (abs_nonneg _) (by positivity)
    simp only [hf, hg]
    nlinarith
  -- integrability
  have hgi : IntervalIntegrable g MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    rw [hg]
    fun_prop
  have hfi : IntervalIntegrable f MeasureTheory.volume 0 L := by
    have h1 : IntervalIntegrable
        (fun t => (t ^ 2 * primeFreeKernel t + t / 2) * e (1 - t / L))
        MeasureTheory.volume 0 L := by
      apply IntervalIntegrable.mono_fun'
        (g := fun t => 3 * t ^ 2 * |e (1 - t / L)|)
      · exact (by fun_prop : Continuous fun t : ℝ => 3 * t ^ 2 * |e (1 - t / L)|).intervalIntegrable
          0 L
      · exact ((((measurable_id.pow_const 2).mul measurable_primeFreeKernel).add
          (measurable_id.div_const 2)).mul hcomp.measurable).aestronglyMeasurable
      · rw [Set.uIoc_of_le hL.le]
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall (fun t ht => ?_))
        show ‖(t ^ 2 * primeFreeKernel t + t / 2) * e (1 - t / L)‖ ≤ 3 * t ^ 2 * |e (1 - t / L)|
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (abs_sq_mul_primeFreeKernel_add_le ht.1 (ht.2.trans hL2)) (abs_nonneg _)
    have h2 : IntervalIntegrable (fun t => t / 2 * e (1 - t / L)) MeasureTheory.volume 0 L :=
      (by fun_prop : Continuous fun t : ℝ => t / 2 * e (1 - t / L)).intervalIntegrable 0 L
    have := h1.sub h2
    refine this.congr (fun t _ => ?_)
    simp only [hf]
    ring
  have hmono := intervalIntegral.integral_mono_on hL.le hgi hfi hfg
  have hgval : ∫ t in (0 : ℝ)..L, g t =
      L ^ 2 / (4 * Real.pi ^ 2) * M - 3 * C * (L ^ 3 / 12) := by
    rw [hg]
    simp only
    rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun t : ℝ => -(t / 2 * e (1 - t / L))).intervalIntegrable 0 L)
        ((by fun_prop : Continuous fun t : ℝ =>
          3 * C * (t ^ 2 * (1 - t / L))).intervalIntegrable 0 L),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      integral_sq_mul_one_sub_div hL]
    have := integral_half_mul_re_energy_index N z hsum hL
    rw [he]
    simp only at this ⊢
    rw [this, hM]
    ring
  have htest : primeFreeSecondTest N z L = ∫ t in (0 : ℝ)..L, f t := rfl
  rw [htest]
  refine le_trans (le_of_eq ?_) hmono
  rw [hgval, hC]
  ring

/-- **M42 positivity radius.**  For nonzero `z` with `∑ z = 0`, `N ≥ 1` and
`0 < L < 1/(2π²(2N+1)N²)` (automatically `< log 2`), `Q_N(L, z) > 0`. -/
theorem primeFreeSecondTest_pos (N : ℕ) (hN : 1 ≤ N) (z : Fin (2 * N + 1) → ℂ)
    (hsum : ∑ i, z i = 0) (hz : z ≠ 0) {L : ℝ} (hL : 0 < L)
    (hLr : L < 1 / (2 * Real.pi ^ 2 * (2 * N + 1) * N ^ 2)) :
    0 < primeFreeSecondTest N z L := by
  have hpi := Real.pi_gt_three
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have h3 : (3 : ℝ) ≤ 2 * N + 1 := by linarith
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hden : 54 ≤ 2 * Real.pi ^ 2 * (2 * N + 1) * N ^ 2 := by
    calc (54 : ℝ) = 2 * 9 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi ^ 2 * (2 * N + 1) * N ^ 2 := by gcongr
  have hL2 : L ≤ Real.log 2 := by
    have hlog := Real.log_two_gt_d9
    have : 1 / (2 * Real.pi ^ 2 * (2 * N + 1) * N ^ 2) ≤ 1 / 54 :=
      one_div_le_one_div_of_le (by norm_num) hden
    linarith
  have hM : 0 < ∑ i, Complex.normSq (z i) := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hge := primeFreeSecondTest_ge N z hsum hL hL2
  have hfac : 0 < 1 / (4 * Real.pi ^ 2) - L * (2 * N + 1) * N ^ 2 / 2 := by
    have hpos : 0 < 2 * Real.pi ^ 2 * (2 * N + 1) * N ^ 2 := by positivity
    rw [lt_div_iff₀ hpos] at hLr
    have h4 : 0 < 4 * Real.pi ^ 2 := by positivity
    rw [sub_pos, lt_div_iff₀ h4]
    nlinarith
  have : 0 < L ^ 2 * (∑ i, Complex.normSq (z i)) *
      (1 / (4 * Real.pi ^ 2) - L * (2 * N + 1) * N ^ 2 / 2) := by positivity
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.norm_sourceEntry_le
#print axioms Zeta23.CCM.norm_quadraticForm_sourceMatrix_le
#print axioms Zeta23.CCM.abs_re_quadraticForm_index_le
#print axioms Zeta23.CCM.abs_sq_mul_primeFreeKernel_add_le
#print axioms Zeta23.CCM.integral_half_mul_re_energy_index
#print axioms Zeta23.CCM.primeFreeSecondTest_ge
#print axioms Zeta23.CCM.primeFreeSecondTest_pos
