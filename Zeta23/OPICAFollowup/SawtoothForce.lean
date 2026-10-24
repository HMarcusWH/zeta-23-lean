import Zeta23.OPICAFollowup.LogFourierSobolev
import Zeta23.OPICAFollowup.ProfileEulerMaclaurin
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
The arithmetic sawtooth force (F1). On t ∈ ℝ the real weight w(t) = e^(-t/2){e^t} is e^(t/2) for
t < 0 and at most e^(-t/2) for t ≥ 0, so w ∈ L¹ ∩ L². The force 𝔤 = -(∂_t + 1/2) w is the actual
tempered distribution built from Mathlib's tempered-distribution derivative of w.

- On compactly supported smooth tests, 𝔤 = Σ_(n ≥ 1) n^(-1/2) δ_(log n) - e^(t/2) dt. Each cell
  [log n, log(n+1)] contributes its left-limit atom and the continuum term, because
  w' + w/2 = e^(t/2) there. The jump at log 1 = 0 is retained. Neither exponentially growing
  summand is transformed separately.
- (F1.3) ∫_0^∞ {x} x^(-s-1) dx = -ζ(s)/s for 0 < Re s < 1 is derived from the Euler-Maclaurin
  continuation of `ProfileEulerMaclaurin` (`zeta_eq_bernoulli`). The substitution x = e^t then
  gives 𝓕_log w(ξ) = -ζ(1/2 + iξ)/(1/2 + iξ), and 𝓕 𝔤 = ζ(1/2 + 2πi·) as a tempered distribution.
- (F1.4) The exact cell integrals give
  ∫_0^L {x}²/x² = 2L - H_L - 2(L-1) log L + 2 log Γ(L), and the limit log(2π) - γ follows from
  Stirling and H_L - log L → γ. The Plancherel theorem of `LogFourierSobolev` then identifies
  this limit with the weighted zeta moment, and 𝔤 ∈ H⁻¹ with constant (log(2π) - γ)^(1/2).
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff

namespace Zeta23.OPICAFollowup

section Norm

lemma fract_sq_div_sq_le_one {x : ℝ} (hx : 0 ≤ x) : Int.fract x ^ 2 / x ^ 2 ≤ 1 := by
  rcases hx.lt_or_eq with hx | hx
  · rw [div_le_one (by positivity)]
    have h1 : Int.fract x ≤ x := by
      have : (0 : ℝ) ≤ ⌊x⌋ := by exact_mod_cast Int.floor_nonneg.mpr hx.le
      rw [Int.fract]; linarith
    exact pow_le_pow_left₀ (Int.fract_nonneg x) h1 2
  · subst hx; simp

lemma fract_sq_div_sq_nonneg (x : ℝ) : 0 ≤ Int.fract x ^ 2 / x ^ 2 := by positivity

lemma measurable_fract_sq_div_sq : Measurable (fun x : ℝ => Int.fract x ^ 2 / x ^ 2) := by
  have : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  fun_prop

lemma intervalIntegrable_fract_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun x : ℝ => Int.fract x ^ 2 / x ^ 2) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    measurable_fract_sq_div_sq.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : 0 ≤ x := by
    rcases le_total a b with hab | hab
    · rw [uIoc_of_le hab] at hx; linarith [hx.1]
    · rw [uIoc_of_ge hab] at hx; linarith [hx.1]
  dsimp only
  rw [Real.norm_eq_abs, abs_of_nonneg (fract_sq_div_sq_nonneg x), norm_one]
  exact fract_sq_div_sq_le_one hx0

/-- The first cell: ∫_0^1 {x}²/x² = 1. -/
lemma integral_fract_sq_zero : ∫ x in (0 : ℝ)..1, Int.fract x ^ 2 / x ^ 2 = 1 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (1 : ℝ)) fun x hx => ?_]
  · simp
  · rw [Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩, div_self (ne_of_gt (pow_pos hx.1 2))]

/-- The cell integrals ∫_n^(n+1) {x}²/x² = 1 + n/(n+1) - 2n log(1 + 1/n), n ≥ 1. -/
lemma integral_fract_sq_cell {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (n : ℝ)..(n + 1), Int.fract x ^ 2 / x ^ 2 =
      1 + n / (n + 1) - 2 * n * Real.log (1 + 1 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hcongr : (∫ x in (n : ℝ)..(n + 1), Int.fract x ^ 2 / x ^ 2) =
      ∫ x in (n : ℝ)..(n + 1), (1 - 2 * n * x⁻¹ + (n : ℝ) ^ 2 * (x ^ 2)⁻¹) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    rw [fract_eq_of_mem_cell (Ioo_subset_Ico_self hx)]
    field_simp; ring
  rw [hcongr]
  have hpos : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := fun x hx => by
    rw [uIcc_of_le hle] at hx; linarith [hx.1]
  have hderiv : ∀ x ∈ uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun y => y - 2 * n * Real.log y - (n : ℝ) ^ 2 * y⁻¹)
        (1 - 2 * n * x⁻¹ + (n : ℝ) ^ 2 * (x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 := hpos x hx
    have h := ((hasDerivAt_id x).sub ((Real.hasDerivAt_log hx0.ne').const_mul (2 * (n : ℝ)))).sub
      ((hasDerivAt_inv hx0.ne').const_mul ((n : ℝ) ^ 2))
    refine h.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun x : ℝ => 1 - 2 * n * x⁻¹ + (n : ℝ) ^ 2 * (x ^ 2)⁻¹) (uIcc (n : ℝ) (n + 1)) := by
    intro x hx
    have hx0 := hpos x hx
    exact (((continuousAt_const.sub (continuousAt_const.mul (continuousAt_inv₀ hx0.ne'))).add
      (continuousAt_const.mul ((continuous_pow 2).continuousAt.inv₀ (by positivity))))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hl : Real.log (1 + 1 / (n : ℝ)) = Real.log ((n : ℝ) + 1) - Real.log n := by
    rw [show 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n by field_simp, Real.log_div (by positivity) hn0.ne']
  rw [hl]
  field_simp
  ring

/-- The exact finite cell norm identity ∫_0^L {x}²/x² = 2L - H_L - 2(L-1) log L + 2 log Γ(L). -/
theorem integral_fract_sq_closed {L : ℕ} (hL : 1 ≤ L) :
    ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2 =
      2 * L - harmonic L - 2 * (L - 1) * Real.log L + 2 * Real.log (Real.Gamma L) := by
  induction L, hL using Nat.le_induction with
  | base => simp [integral_fract_sq_zero, harmonic, Real.Gamma_one]; norm_num
  | succ L hL ih =>
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    rw [Nat.cast_succ, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fract_sq le_rfl hL0.le) (intervalIntegrable_fract_sq hL0.le (by linarith)),
      ih, integral_fract_sq_cell hL, harmonic_succ, Real.Gamma_add_one hL0.ne',
      Real.log_mul hL0.ne' (Real.Gamma_pos_of_pos hL0).ne']
    have hl : Real.log (1 + 1 / (L : ℝ)) = Real.log ((L : ℝ) + 1) - Real.log L := by
      rw [show 1 + 1 / (L : ℝ) = ((L : ℝ) + 1) / L by field_simp, Real.log_div (by positivity) hL0.ne']
    rw [hl]
    push_cast
    field_simp
    ring

/-- The closed form rewritten with the Stirling sequence. -/
lemma integral_fract_sq_stirling {L : ℕ} (hL : 1 ≤ L) :
    ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2 =
      -(harmonic L - Real.log L) + 2 * Real.log (Stirling.stirlingSeq L) + Real.log 2 := by
  rw [integral_fract_sq_closed hL]
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hG : Real.Gamma ((k + 1 : ℕ) : ℝ) = Nat.factorial k := by
    rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]
  have hf : ((Nat.factorial (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * Nat.factorial k := by push_cast [Nat.factorial_succ]; ring
  have hfac : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  have hs : Real.log (Stirling.stirlingSeq (k + 1)) = Real.log ((k : ℝ) + 1) + Real.log (Nat.factorial k : ℝ) -
      (Real.log 2 + Real.log ((k : ℝ) + 1)) / 2 - ((k : ℝ) + 1) * (Real.log ((k : ℝ) + 1) - 1) := by
    rw [Stirling.stirlingSeq]
    push_cast
    rw [hf, Real.log_div (by positivity) (by positivity), Real.log_mul hk.ne' hfac.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
      Real.log_pow, Real.log_div hk.ne' (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_mul (by norm_num) hk.ne']
    push_cast
    ring
  rw [hG, hs]
  push_cast
  ring

lemma tendsto_integral_fract_sq :
    Tendsto (fun L : ℕ => ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2) atTop
      (𝓝 (Real.log (2 * π) - Real.eulerMascheroniConstant)) := by
  have hS := (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).const_mul 2
  have h := (Real.tendsto_harmonic_sub_log.neg.add hS).add_const (Real.log 2)
  have hval : -Real.eulerMascheroniConstant + 2 * Real.log √π + Real.log 2 =
      Real.log (2 * π) - Real.eulerMascheroniConstant := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']; ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  exact (integral_fract_sq_stirling hL).symm

lemma integrableOn_fract_sq : IntegrableOn (fun x : ℝ => Int.fract x ^ 2 / x ^ 2) (Ioi 0) := by
  have hdom : IntegrableOn (fun x : ℝ => (Ioc 0 1).indicator (fun _ => (1 : ℝ)) x +
      (Ioi 1).indicator (fun x => x ^ (-2 : ℝ)) x) (Ioi 0) := by
    refine Integrable.add ?_ ?_
    · refine ((integrable_indicator_iff measurableSet_Ioc).mpr ?_).mono_measure Measure.restrict_le_self
      exact integrableOn_const (by simp) (by simp)
    · exact ((integrable_indicator_iff measurableSet_Ioi).mpr
        (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)).mono_measure Measure.restrict_le_self
  refine hdom.mono' measurable_fract_sq_div_sq.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (fract_sq_div_sq_nonneg x)]
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [indicator_of_mem (show x ∈ Ioc 0 1 from ⟨hx0, hx1⟩),
      indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr hx1), add_zero]
    exact fract_sq_div_sq_le_one hx0.le
  · rw [indicator_of_notMem (show x ∉ Ioc 0 1 from fun h => absurd h.2 (not_le.mpr hx1)),
      indicator_of_mem (show x ∈ Ioi 1 from hx1), zero_add, Real.rpow_neg hx0.le, Real.rpow_two]
    rw [div_eq_mul_inv]
    refine mul_le_of_le_one_left (by positivity) ?_
    have h0 := Int.fract_nonneg x; have h1 := Int.fract_lt_one x
    nlinarith

/-- ∫_0^∞ {x}²/x² = log(2π) - γ. -/
theorem integral_fract_sq : ∫ x in Ioi (0 : ℝ), Int.fract x ^ 2 / x ^ 2 =
    Real.log (2 * π) - Real.eulerMascheroniConstant :=
  tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 integrableOn_fract_sq
    tendsto_natCast_atTop_atTop) tendsto_integral_fract_sq

end Norm

section Weight

/-- The real sawtooth weight w(t) = e^(-t/2) {e^t}. -/
def sawtoothWeight (t : ℝ) : ℂ := ((Real.exp (-t / 2) * Int.fract (Real.exp t) : ℝ) : ℂ)

lemma norm_sawtoothWeight_sq (t : ℝ) :
    ‖sawtoothWeight t‖ ^ 2 = Real.exp t * (Int.fract (Real.exp t) ^ 2 / Real.exp t ^ 2) := by
  rw [sawtoothWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    show Real.exp (-t / 2) ^ 2 = (Real.exp t)⁻¹ by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]; ring_nf]
  field_simp

lemma measurable_sawtoothWeight : Measurable sawtoothWeight := by
  have : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  unfold sawtoothWeight; fun_prop

/-- ‖w‖₂² = ∫_0^∞ {x}²/x² = log(2π) - γ. -/
theorem integral_norm_sq_sawtoothWeight :
    ∫ t, ‖sawtoothWeight t‖ ^ 2 = Real.log (2 * π) - Real.eulerMascheroniConstant := by
  simp_rw [norm_sawtoothWeight_sq]
  rw [← integral_fract_sq]
  exact integral_exp_smul_comp (fun x => Int.fract x ^ 2 / x ^ 2)

theorem memLp_two_sawtoothWeight : MemLp sawtoothWeight 2 := by
  refine (memLp_two_iff_integrable_sq_norm measurable_sawtoothWeight.aestronglyMeasurable).mpr ?_
  simp_rw [norm_sawtoothWeight_sq]
  exact (integrable_exp_smul_comp_iff (fun x => Int.fract x ^ 2 / x ^ 2)).mpr integrableOn_fract_sq

end Weight

section Mellin

lemma ofReal_mul_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  conv_rhs => rw [show -s = 1 + (-s - 1) by ring, Complex.cpow_add _ _ hx', Complex.cpow_one]

/-- (F1.3): for 0 < Re s < 1, ∫_0^∞ {x} x^(-s-1) dx = -ζ(s)/s, absolutely convergent. -/
theorem mellin_fract {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = -riemannZeta s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  set F : ℝ → ℂ := fun x => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) with hF
  have hre : (-s - 1).re < -1 := by simp; linarith
  -- (0, 1]: F = x^(-s) a.e.
  have hEq : EqOn F (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioo 0 1) := fun x hx => by
    simp only [hF, Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩, ofReal_mul_cpow hx.1]
  have hI01 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioc 0 1) := by
    have := intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (r := -s) (by simp; linarith)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
  have hF01 : IntegrableOn F (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hI01 ⊢
    exact hI01.congr_fun hEq.symm measurableSet_Ioo
  have hint01 : ∫ x in Ioc (0 : ℝ) 1, F x = 1 / (1 - s) := by
    rw [integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hEq,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_cpow (Or.inl (by simp; linarith))]
    rw [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
      Complex.zero_cpow (by rw [show -s + 1 = 1 - s by ring]; exact hs1'), show -s + 1 = 1 - s by ring]
    ring
  -- (1, ∞): {x} = B₁(x) + 1/2
  have hB : IntegrableOn (fun x : ℝ => (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    integrableOn_bounded_mul_cpow measurable_bernoulliOneRight abs_bernoulliOneRight_le hre one_pos
  have hP : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt hre one_pos
  have hsplit : EqOn F (fun x : ℝ => (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s - 1) +
      (1 / 2 : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := fun x _ => by
    simp only [hF, bernoulliOneRight]; push_cast; ring
  have hF1 : IntegrableOn F (Ioi 1) := (hB.add (hP.const_mul _)).congr_fun hsplit.symm measurableSet_Ioi
  have hint1 : ∫ x in Ioi (1 : ℝ), F x = zetaBernoulliIntegral s + 1 / (2 * s) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add hB (hP.const_mul _),
      integral_const_mul, integral_Ioi_cpow_of_lt hre one_pos, zetaBernoulliIntegral]
    rw [Complex.ofReal_one, Complex.one_cpow, show -s - 1 + 1 = -s by ring]
    field_simp
  have hU : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  refine ⟨by rw [hU]; exact hF01.union hF1, ?_⟩
  rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hF01 hF1, hint01, hint1,
    zeta_eq_bernoulli h0 hs1]
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

end Mellin

section LogFourierWeight

lemma ofReal_exp_cpow (t : ℝ) (z : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ z = Complex.exp (t * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

/-- The substitution x = e^t turns e^(-iξt) w(t) into e^t {x} x^(-s-1), s = 1/2 + iξ. -/
lemma sawtooth_kernel_eq (ξ t : ℝ) :
    cexp (-((ξ * t : ℝ) : ℂ) * I) * sawtoothWeight t =
      Real.exp t • (((Int.fract (Real.exp t) : ℝ) : ℂ) *
        ((Real.exp t : ℝ) : ℂ) ^ (-(1 / 2 + ξ * I) - 1)) := by
  rw [ofReal_exp_cpow, sawtoothWeight, Complex.real_smul]
  push_cast
  set F : ℂ := ((Int.fract (Real.exp t) : ℝ) : ℂ)
  have e : -(↑ξ * ↑t) * I + -↑t / 2 = ↑t + ↑t * (-(1 / 2 + ↑ξ * I) - 1) := by ring
  calc cexp (-(↑ξ * ↑t) * I) * (cexp (-↑t / 2) * F) = F * cexp (-(↑ξ * ↑t) * I + -↑t / 2) := by
        rw [Complex.exp_add]; ring
    _ = F * cexp (↑t + ↑t * (-(1 / 2 + ↑ξ * I) - 1)) := by rw [e]
    _ = cexp ↑t * (F * cexp (↑t * (-(1 / 2 + ↑ξ * I) - 1))) := by rw [Complex.exp_add]; ring

theorem integrable_sawtoothWeight : Integrable sawtoothWeight := by
  have h := (integrable_exp_smul_comp_iff (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) *
    (x : ℂ) ^ (-(1 / 2 + (0 : ℝ) * I) - 1))).mpr (mellin_fract (by simp) (by simp; norm_num)).1
  refine h.congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [← sawtooth_kernel_eq 0 t]; simp

/-- (F1.2) for w: 𝓕_log w(ξ) = -ζ(1/2 + iξ)/(1/2 + iξ). -/
theorem logFourier_sawtoothWeight (ξ : ℝ) :
    logFourier sawtoothWeight ξ = -riemannZeta (1 / 2 + ξ * I) / (1 / 2 + ξ * I) := by
  have hs0 : 0 < (1 / 2 + ξ * I : ℂ).re := by norm_num
  have hs1 : (1 / 2 + ξ * I : ℂ).re < 1 := by norm_num
  rw [logFourier]
  simp_rw [sawtooth_kernel_eq ξ]
  rw [integral_exp_smul_comp (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(1 / 2 + ξ * I) - 1))]
  exact (mellin_fract hs0 hs1).2

end LogFourierWeight

section Moment

lemma norm_logFourier_sawtooth_sq (ξ : ℝ) :
    ‖logFourier sawtoothWeight ξ‖ ^ 2 = ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4) := by
  rw [logFourier_sawtoothWeight, norm_div, norm_neg, div_pow]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, show (1 / 2 + ξ * I : ℂ) = ((1 / 2 : ℝ) : ℂ) + (ξ : ℂ) * I by
    push_cast; ring, Complex.normSq_add_mul_I]
  ring

/-- (F1.4): ‖w‖₂² = log(2π) - γ = (1/2π) ∫ |ζ(1/2 + iξ)|²/(ξ² + 1/4) dξ, with the weighted
moment absolutely convergent. -/
theorem sawtooth_weighted_zeta_moment :
    Integrable (fun ξ : ℝ => ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4)) ∧
    (∫ t, ‖sawtoothWeight t‖ ^ 2) = Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    1 / (2 * π) * ∫ ξ : ℝ, ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4) =
      Real.log (2 * π) - Real.eulerMascheroniConstant := by
  obtain ⟨hI, hE⟩ := logFourier_plancherel integrable_sawtoothWeight memLp_two_sawtoothWeight
  simp_rw [norm_logFourier_sawtooth_sq] at hI hE
  exact ⟨hI, integral_norm_sq_sawtoothWeight, hE ▸ integral_norm_sq_sawtoothWeight⟩

end Moment

section Force

/-- w as a tempered distribution (through its L² class). -/
def sawtoothWeightTD : 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistribution (memLp_two_sawtoothWeight.toLp sawtoothWeight)

/-- The actual tempered force 𝔤 = -(∂_t + 1/2) w. -/
def nativeLogForce : 𝓢'(ℝ, ℂ) :=
  -(TemperedDistribution.derivCLM ℂ sawtoothWeightTD) - (1 / 2 : ℂ) • sawtoothWeightTD

lemma sawtoothWeightTD_apply (φ : 𝓢(ℝ, ℂ)) : sawtoothWeightTD φ = ∫ t, φ t * sawtoothWeight t := by
  rw [sawtoothWeightTD, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [memLp_two_sawtoothWeight.coeFn_toLp] with t ht
  rw [ht, smul_eq_mul]

lemma integrable_mul_sawtooth {φ : ℝ → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ t, ‖φ t‖ ≤ C) :
    Integrable (fun t => sawtoothWeight t * φ t) :=
  integrable_sawtoothWeight.mul_bdd hφ.aestronglyMeasurable (Eventually.of_forall hC)

/-- ⟨𝔤, φ⟩ = ∫ w (φ' - φ/2) on Schwartz tests. -/
theorem nativeLogForce_apply (φ : 𝓢(ℝ, ℂ)) :
    nativeLogForce φ = ∫ t, sawtoothWeight t * (deriv φ t - φ t / 2) := by
  obtain ⟨C0, hC0⟩ := φ.decay 0 0
  obtain ⟨C1, hC1⟩ := (SchwartzMap.derivCLM ℂ ℂ φ).decay 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC0 hC1
  have hI0 := integrable_mul_sawtooth φ.continuous hC0.2
  have hI1 := integrable_mul_sawtooth (SchwartzMap.derivCLM ℂ ℂ φ).continuous hC1.2
  simp only [SchwartzMap.derivCLM_apply] at hI1
  simp only [nativeLogForce, sub_apply, neg_apply,
    smul_apply, TemperedDistribution.derivCLM_apply_apply, map_neg,
    sawtoothWeightTD_apply, SchwartzMap.derivCLM_apply, smul_eq_mul]
  rw [neg_neg, ← integral_const_mul,
    ← integral_sub (hI1.congr (Eventually.of_forall fun t => mul_comm _ _))
      ((hI0.const_mul (1 / 2)).congr (Eventually.of_forall fun t => by ring))]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only; ring

end Force

section CompactTests

lemma exp_log_half {m : ℝ} (hm : 0 < m) : Real.exp (Real.log m / 2) = m ^ (1 / 2 : ℝ) := by
  rw [Real.rpow_def_of_pos hm]; ring_nf

lemma exp_neg_log_half {m : ℝ} (hm : 0 < m) : Real.exp (-Real.log m / 2) = m ^ (-(1 / 2) : ℝ) := by
  rw [Real.rpow_def_of_pos hm]; ring_nf

lemma sawtooth_integral_congr_Ioo {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- Integration by parts of a smooth branch b with b' + b/2 = e^(t/2) against φ' - φ/2. -/
lemma branch_parts {b b' φ φ' : ℝ → ℂ} {α β : ℝ} (hbd : ∀ t, HasDerivAt b (b' t) t)
    (hb'c : Continuous b') (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    (hsum : ∀ t, b' t + b t / 2 = (Real.exp (t / 2) : ℂ)) :
    ∫ t in α..β, b t * (φ' t - φ t / 2) =
      b β * φ β - b α * φ α - ∫ t in α..β, (Real.exp (t / 2) : ℂ) * φ t := by
  have hbc : Continuous b := continuous_iff_continuousAt.mpr fun t => (hbd t).continuousAt
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
    (fun t _ => hbd t) (fun t _ => hφ t) (hb'c.intervalIntegrable _ _) (hφ'.intervalIntegrable _ _)
  have e1 : (∫ t in α..β, b t * (φ' t - φ t / 2)) =
      (∫ t in α..β, b t * φ' t) - ∫ t in α..β, b t * φ t / 2 := by
    rw [← intervalIntegral.integral_sub (f := fun t => b t * φ' t) (g := fun t => b t * φ t / 2)
      ((hbc.mul hφ').intervalIntegrable _ _) (((hbc.mul hφc).div_const 2).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [e1, hparts, sub_sub, ← intervalIntegral.integral_add (f := fun t => b' t * φ t)
    (g := fun t => b t * φ t / 2) ((hb'c.mul hφc).intervalIntegrable _ _)
    (((hbc.mul hφc).div_const 2).intervalIntegrable _ _)]
  congr 1
  exact intervalIntegral.integral_congr fun t _ => by
    rw [← hsum t]; ring

/-- The cell [log n, log(n+1)], n ≥ 1: w = e^(t/2) - n e^(-t/2) there, w' + w/2 = e^(t/2), and
the only boundary contribution is the left limit (n+1)^(-1/2) at the right end. -/
lemma sawtooth_cell {n : ℕ} (hn : 1 ≤ n) {φ φ' : ℝ → ℂ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') :
    ∫ t in Real.log n..Real.log (n + 1), sawtoothWeight t * (φ' t - φ t / 2) =
      ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
        ∫ t in Real.log n..Real.log (n + 1), (Real.exp (t / 2) : ℂ) * φ t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  have hle : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hn0 (by linarith)
  set b : ℝ → ℂ := fun t => ((Real.exp (t / 2) - n * Real.exp (-t / 2) : ℝ) : ℂ) with hb
  set b' : ℝ → ℂ := fun t => ((Real.exp (t / 2) / 2 + n * Real.exp (-t / 2) / 2 : ℝ) : ℂ) with hb'
  have hbd : ∀ t, HasDerivAt b (b' t) t := by
    intro t
    have h1 := (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
    have h2 := ((Real.hasDerivAt_exp (-t / 2)).comp t ((hasDerivAt_id t).neg.div_const 2)).const_mul (n : ℝ)
    refine (h1.sub h2).ofReal_comp.congr_deriv ?_
    simp only [hb']; push_cast; ring
  have hb'c : Continuous b' := by simp only [hb']; fun_prop
  have hsum : ∀ t, b' t + b t / 2 = (Real.exp (t / 2) : ℂ) := fun t => by
    simp only [hb, hb']; push_cast; ring
  have hcell : EqOn (fun t => sawtoothWeight t * (φ' t - φ t / 2)) (fun t => b t * (φ' t - φ t / 2))
      (Ioo (Real.log n) (Real.log (n + 1))) := by
    intro t ht
    have h1 : (n : ℝ) < Real.exp t := by rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr ht.1
    have h2 : Real.exp t < n + 1 := by rw [← Real.exp_log hn1]; exact Real.exp_lt_exp.mpr ht.2
    have hfr : Int.fract (Real.exp t) = Real.exp t - n := by
      have hfl : ⌊Real.exp t⌋ = (n : ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [Int.fract, hfl]; push_cast; ring
    have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by rw [← Real.exp_add]; ring_nf
    simp only [sawtoothWeight, hb, hfr]
    congr 1
    congr 1
    rw [mul_sub, he]; ring
  rw [sawtooth_integral_congr_Ioo hle hcell, branch_parts hbd hb'c hφ hφ' hsum]
  have hbR : b (Real.log (n + 1)) = ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    simp only [hb, exp_log_half hn1, exp_neg_log_half hn1]
    congr 1
    have h := Real.rpow_add hn1 (1 / 2) (-(1 / 2))
    have h' : ((n : ℝ) + 1) ^ (1 / 2 : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_one_add' hn1.le (by norm_num)]; norm_num
    rw [h']; ring
  have hbL : b (Real.log n) = 0 := by
    simp only [hb, exp_log_half hn0, exp_neg_log_half hn0]
    have h' : (n : ℝ) ^ (1 / 2 : ℝ) = n * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_one_add' hn0.le (by norm_num)]; norm_num
    rw [h', sub_self, Complex.ofReal_zero]
  rw [hbR, hbL, zero_mul, sub_zero]

/-- The first cell (-A, 0): w = e^(t/2) there. -/
lemma sawtooth_cell_zero {A : ℝ} (hA : 0 ≤ A) {φ φ' : ℝ → ℂ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') :
    ∫ t in (-A)..0, sawtoothWeight t * (φ' t - φ t / 2) =
      φ 0 - (Real.exp (-A / 2) : ℂ) * φ (-A) - ∫ t in (-A)..0, (Real.exp (t / 2) : ℂ) * φ t := by
  set b : ℝ → ℂ := fun t => ((Real.exp (t / 2) : ℝ) : ℂ) with hb
  set b' : ℝ → ℂ := fun t => ((Real.exp (t / 2) / 2 : ℝ) : ℂ) with hb'
  have hbd : ∀ t, HasDerivAt b (b' t) t := by
    intro t
    refine ((Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).ofReal_comp.congr_deriv ?_
    simp only [hb']; push_cast; ring
  have hb'c : Continuous b' := by simp only [hb']; fun_prop
  have hsum : ∀ t, b' t + b t / 2 = (Real.exp (t / 2) : ℂ) := fun t => by
    simp only [hb, hb']; push_cast; ring
  have hcell : EqOn (fun t => sawtoothWeight t * (φ' t - φ t / 2)) (fun t => b t * (φ' t - φ t / 2))
      (Ioo (-A) 0) := by
    intro t ht
    have hfr : Int.fract (Real.exp t) = Real.exp t :=
      Int.fract_eq_self.mpr ⟨(Real.exp_pos t).le, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr ht.2⟩
    have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by rw [← Real.exp_add]; ring_nf
    simp only [sawtoothWeight, hb, hfr, he]
  rw [sawtooth_integral_congr_Ioo (by linarith) hcell, branch_parts hbd hb'c hφ hφ' hsum]
  simp only [hb, zero_div, Real.exp_zero, Complex.ofReal_one, one_mul, neg_div]

lemma intervalIntegrable_sawtooth_mul {c : ℝ → ℂ} (hc : Continuous c) (a b : ℝ) :
    IntervalIntegrable (fun t => sawtoothWeight t * c t) volume a b :=
  (integrable_sawtoothWeight.intervalIntegrable).mul_continuousOn hc.continuousOn

/-- Telescoped cells: ∫_(-A)^(log(N+1)) w (φ' - φ/2) with the atoms at log 1, ..., log(N+1). -/
lemma sawtooth_telescoping {A : ℝ} (hA : 0 ≤ A) {φ φ' : ℝ → ℂ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') (N : ℕ) :
    ∫ t in (-A)..Real.log ((N : ℝ) + 1), sawtoothWeight t * (φ' t - φ t / 2) =
      ∑ m ∈ Finset.range (N + 1), ((((m : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (m + 1)) -
        (Real.exp (-A / 2) : ℂ) * φ (-A) -
        ∫ t in (-A)..Real.log ((N : ℝ) + 1), (Real.exp (t / 2) : ℂ) * φ t := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt
  have hII : ∀ a b : ℝ, IntervalIntegrable (fun t => sawtoothWeight t * (φ' t - φ t / 2)) volume a b :=
    intervalIntegrable_sawtooth_mul (hφ'.sub (hφc.div_const 2))
  have hEI : ∀ a b : ℝ, IntervalIntegrable (fun t => (Real.exp (t / 2) : ℂ) * φ t) volume a b :=
    fun a b => ((by fun_prop : Continuous fun t : ℝ => (Real.exp (t / 2) : ℂ)).mul hφc).intervalIntegrable a b
  induction N with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_add, Real.log_one, Finset.range_one, Finset.sum_singleton,
      Real.one_rpow, Complex.ofReal_one, one_mul]
    exact sawtooth_cell_zero hA hφ hφ'
  | succ N ih =>
    have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hcell := sawtooth_cell (n := N + 1) (by omega) hφ hφ'
    rw [hc] at hcell
    rw [hc, ← intervalIntegral.integral_add_adjacent_intervals (hII _ (Real.log ((N : ℝ) + 1))) (hII _ _),
      ih, hcell, ← intervalIntegral.integral_add_adjacent_intervals (hEI (-A) (Real.log ((N : ℝ) + 1)))
        (hEI _ (Real.log ((N : ℝ) + 1 + 1))), Finset.sum_range_succ _ (N + 1)]
    push_cast
    ring

lemma eventually_zero_right_of_compact {φ : ℝ → ℂ} (hc : HasCompactSupport φ) :
    ∃ M : ℝ, ∀ x, M < x → φ =ᶠ[𝓝 x] 0 := by
  obtain ⟨M, hM⟩ := hc.isCompact.bddAbove
  refine ⟨M, fun x hx => ?_⟩
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport fun h => absurd (hM h) (not_le.mpr hy)

lemma eventually_zero_left_of_compact {φ : ℝ → ℂ} (hc : HasCompactSupport φ) :
    ∃ m : ℝ, ∀ x, x < m → φ =ᶠ[𝓝 x] 0 := by
  obtain ⟨m, hm⟩ := hc.isCompact.bddBelow
  refine ⟨m, fun x hx => ?_⟩
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport fun h => absurd (hm h) (not_le.mpr hy)

/-- (F1.1) on compactly supported smooth tests: ∫ w (φ' - φ/2) = Σ_(n ≥ 1) n^(-1/2) φ(log n) - ∫ e^(t/2) φ. -/
theorem sawtooth_compact_identity {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ t, sawtoothWeight t * (deriv φ t - φ t / 2) =
      ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
        ∫ t, (Real.exp (t / 2) : ℂ) * φ t := by
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.differentiable (by simp)).differentiableAt).hasDerivAt
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := eventually_zero_right_of_compact hc
  obtain ⟨m, hm⟩ := eventually_zero_left_of_compact hc
  have hzR : ∀ x, M < x → φ x = 0 ∧ deriv φ x = 0 := fun x hx =>
    ⟨(hM x hx).self_of_nhds, by rw [(hM x hx).deriv_eq]; simp⟩
  have hzL : ∀ x, x < m → φ x = 0 ∧ deriv φ x = 0 := fun x hx =>
    ⟨(hm x hx).self_of_nhds, by rw [(hm x hx).deriv_eq]; simp⟩
  set A : ℝ := |m| + 1
  have hA : 0 ≤ A := by positivity
  have hAm : -A < m := by have := neg_abs_le m; linarith
  set N : ℕ := ⌈Real.exp M⌉₊
  have hN : M < Real.log ((N : ℝ) + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  have hlt : -A < Real.log ((N : ℝ) + 1) := by
    have : m ≤ M ∨ M < m := le_or_gt m M
    rcases this with h | h
    · linarith
    · -- empty support: both sides vanish
      have hz : ∀ x, φ x = 0 := fun x => by
        rcases lt_or_ge x m with hx | hx
        · exact (hzL x hx).1
        · exact (hzR x (by linarith)).1
      have hA0 : 0 < A := by positivity
      have := Real.log_nonneg (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith : (1 : ℝ) ≤ (N : ℝ) + 1)
      linarith
  have hconv : ∀ F : ℝ → ℂ, (∀ x, x ≤ -A ∨ Real.log ((N : ℝ) + 1) < x → F x = 0) →
      ∫ t, F t = ∫ t in (-A)..Real.log ((N : ℝ) + 1), F t := by
    intro F hF
    rw [intervalIntegral.integral_of_le hlt.le]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hF x ?_).symm
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  have hout : ∀ x, x ≤ -A ∨ Real.log ((N : ℝ) + 1) < x → φ x = 0 ∧ deriv φ x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · exact hzL x (by linarith)
    · exact hzR x (by linarith)
  rw [hconv _ (fun x hx => by simp [(hout x hx).1, (hout x hx).2]),
    hconv _ (fun x hx => by simp [(hout x hx).1]), sawtooth_telescoping hA hd hφ' N,
    (hout (-A) (Or.inl le_rfl)).1, mul_zero, sub_zero]
  congr 1
  refine (tsum_eq_sum (s := Finset.range (N + 1)) fun n hn => ?_).symm
  have hn' : N + 1 ≤ n := not_lt.mp (Finset.mem_range.not.mp hn)
  have : Real.log ((N : ℝ) + 1) < Real.log ((n : ℝ) + 1) :=
    Real.log_lt_log (by positivity) (by exact_mod_cast Nat.lt_succ_of_le hn')
  rw [(hout _ (Or.inr this)).1, mul_zero]

/-- The jump of w at every t = log n, n ≥ 1 (including n = 1): the left limit is n^(-1/2) and the
value is 0. -/
theorem sawtooth_jump {n : ℕ} (hn : 1 ≤ n) :
    Tendsto sawtoothWeight (𝓝[<] (Real.log n)) (𝓝 ((((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) ∧
      sawtoothWeight (Real.log n) = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · set c : ℝ := (n : ℝ) - 1
    set br : ℝ → ℂ := fun t => ((Real.exp (t / 2) - c * Real.exp (-t / 2) : ℝ) : ℂ) with hbr
    have hbrc : Continuous br := by simp only [hbr]; fun_prop
    have hval : br (Real.log n) = ((((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) := by
      simp only [hbr, exp_log_half hn0, exp_neg_log_half hn0, c]
      congr 1
      have h' : (n : ℝ) ^ (1 / 2 : ℝ) = n * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_one_add' hn0.le (by norm_num)]; norm_num
      rw [h']; ring
    have ha : Real.log ((n : ℝ) - 1 / 2) < Real.log n := Real.log_lt_log (by linarith) (by linarith)
    have hev : sawtoothWeight =ᶠ[𝓝[<] (Real.log n)] br := by
      filter_upwards [Ioo_mem_nhdsLT ha] with t ht
      have h1 : (n : ℝ) - 1 / 2 < Real.exp t := by
        rw [← Real.exp_log (by linarith : (0 : ℝ) < n - 1 / 2)]; exact Real.exp_lt_exp.mpr ht.1
      have h2 : Real.exp t < n := by rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr ht.2
      have hfl : ⌊Real.exp t⌋ = ((n - 1 : ℕ) : ℤ) := by
        rw [Int.floor_eq_iff]; push_cast [Nat.cast_sub hn]; constructor <;> linarith
      have hfr : Int.fract (Real.exp t) = Real.exp t - c := by
        rw [Int.fract, hfl]; push_cast [Nat.cast_sub hn]; ring
      have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by rw [← Real.exp_add]; ring_nf
      simp only [sawtoothWeight, hbr, hfr]
      congr 1; rw [mul_sub, he]; ring
    rw [← hval]
    exact (hbrc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  · simp [sawtoothWeight, Real.exp_log hn0]

end CompactTests

section ForceFourier

lemma fourier_sawtoothWeight (η : ℝ) :
    𝓕 sawtoothWeight η = -riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) / (1 / 2 + (2 * π * η : ℝ) * I) := by
  rw [← logFourier_sawtoothWeight, logFourier_eq_fourier]
  field_simp

/-- (F1.2) for 𝔤: the Fourier transform of the tempered force is the function ζ(1/2 + 2πiη)
(Mathlib convention 𝓕 φ(η) = ∫ e^(-2πixη) φ(x) dx; in the log convention ξ = 2πη this is
𝓕_log 𝔤(ξ) = ζ(1/2 + iξ)). -/
theorem fourier_nativeLogForce (φ : 𝓢(ℝ, ℂ)) :
    (𝓕 nativeLogForce) φ = ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * φ η := by
  rw [TemperedDistribution.fourier_apply, nativeLogForce_apply, SchwartzMap.fourier_coe]
  have hφI : Integrable (fun x => φ x) := φ.integrable
  have hxφ : Integrable (fun x : ℝ => x • φ x) := by
    refine (φ.integrable_pow_mul volume 1).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, pow_one]
  have hcφ : Integrable (fun x : ℝ => (-2 * π * I * x) • φ x) := by
    have := hxφ.const_mul (-2 * π * I)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Complex.real_smul, smul_eq_mul]; ring
  rw [Real.deriv_fourier hφI hxφ]
  have hw := integrable_sawtoothWeight
  have h1 : (∫ t, sawtoothWeight t * 𝓕 (fun x : ℝ => (-2 * π * I * x) • φ x) t) =
      ∫ η, 𝓕 sawtoothWeight η * ((-2 * π * I * η) • φ η) :=
    (integral_fourier_mul_eq_of_integrable' hw hcφ).symm
  have h2 : (∫ t, sawtoothWeight t * 𝓕 (fun x => φ x) t) = ∫ η, 𝓕 sawtoothWeight η * φ η :=
    (integral_fourier_mul_eq_of_integrable' hw hφI).symm
  have hF1 : Integrable (fun t => sawtoothWeight t * 𝓕 (fun x : ℝ => (-2 * π * I * x) • φ x) t) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖𝓕 (fun x : ℝ => (-2 * π * I * x) • φ x) t‖ ≤ C :=
      ⟨_, fun t => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ t⟩
    exact hw.mul_bdd (continuous_fourier_of_integrable hcφ).aestronglyMeasurable (Eventually.of_forall hC)
  have hF2 : Integrable (fun t => sawtoothWeight t * 𝓕 (fun x => φ x) t) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖𝓕 (fun x => φ x) t‖ ≤ C :=
      ⟨_, fun t => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ t⟩
    exact hw.mul_bdd (continuous_fourier_of_integrable hφI).aestronglyMeasurable (Eventually.of_forall hC)
  have hsplit : (∫ t, sawtoothWeight t * (𝓕 (fun x : ℝ => (-2 * π * I * x) • φ x) t - 𝓕 (fun x => φ x) t / 2)) =
      (∫ t, sawtoothWeight t * 𝓕 (fun x : ℝ => (-2 * π * I * x) • φ x) t) -
        (1 / 2) * ∫ t, sawtoothWeight t * 𝓕 (fun x => φ x) t := by
    rw [← integral_const_mul, ← integral_sub hF1 (hF2.const_mul _)]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  have hG1 : Integrable (fun η => 𝓕 sawtoothWeight η * ((-2 * π * I * η) • φ η)) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖𝓕 sawtoothWeight t‖ ≤ C :=
      ⟨_, fun t => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ t⟩
    exact hcφ.bdd_mul (continuous_fourier_of_integrable hw).aestronglyMeasurable (Eventually.of_forall hC)
  have hG2 : Integrable (fun η => 𝓕 sawtoothWeight η * φ η) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖𝓕 sawtoothWeight t‖ ≤ C :=
      ⟨_, fun t => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ t⟩
    exact hφI.bdd_mul (continuous_fourier_of_integrable hw).aestronglyMeasurable (Eventually.of_forall hC)
  rw [hsplit, h1, h2, ← integral_const_mul, ← integral_sub hG1 (hG2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [fourier_sawtoothWeight, smul_eq_mul]
  set z : ℂ := 1 / 2 + ((2 * π * η : ℝ) : ℂ) * I with hz
  have hne : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hz] at this
  have hc : (-2 * (π : ℂ) * I * (η : ℂ)) = -(z - 1 / 2) := by rw [hz]; push_cast; ring
  rw [hc]
  field_simp
  ring

end ForceFourier

section Roots

lemma sawtoothWeight_of_neg {t : ℝ} (ht : t < 0) : sawtoothWeight t = (Real.exp (t / 2) : ℂ) := by
  have hfr : Int.fract (Real.exp t) = Real.exp t :=
    Int.fract_eq_self.mpr ⟨(Real.exp_pos t).le, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr ht⟩
  have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by rw [← Real.exp_add]; ring_nf
  simp only [sawtoothWeight, hfr, he]

lemma norm_sawtoothWeight_le (t : ℝ) : ‖sawtoothWeight t‖ ≤ Real.exp (-t / 2) := by
  rw [sawtoothWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _))]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le

/-- A Schwartz test is an H¹(ℝ) element with its derivative. -/
lemma logH1_schwartz (φ : 𝓢(ℝ, ℂ)) : LogH1 φ (deriv φ) := by
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x => (φ.differentiableAt).hasDerivAt
  have e : ⇑(SchwartzMap.derivCLM ℂ ℂ φ) = deriv φ := funext fun x => SchwartzMap.derivCLM_apply ℂ φ x
  have hc : Continuous (deriv φ) := e ▸ (SchwartzMap.derivCLM ℂ ℂ φ).continuous
  refine ⟨fun a b => (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable _ _)).symm, fun a b => hc.intervalIntegrable a b, hc.measurable,
    φ.memLp 2, ?_⟩
  exact e ▸ (SchwartzMap.derivCLM ℂ ℂ φ).memLp 2

/-- F1: the real sawtooth weight w(t) = e^(-t/2){e^t} is in L¹ ∩ L² (w = e^(t/2) for t < 0 and
|w| ≤ e^(-t/2)); the tempered distribution 𝔤 = -(∂_t + 1/2) w acts on Schwartz tests by
∫ w (φ' - φ/2); on compactly supported smooth tests it is the difference
Σ_(n ≥ 1) n^(-1/2) δ_(log n) - e^(t/2) dt (neither exponentially growing summand is transformed
separately); and at every t = log n, n ≥ 1 (n = 1 included), w jumps from n^(-1/2) to 0. -/
theorem sawtooth_integrable_force_identity :
    Integrable sawtoothWeight ∧ MemLp sawtoothWeight 2 ∧
    (∀ t : ℝ, t < 0 → sawtoothWeight t = (Real.exp (t / 2) : ℂ)) ∧
    (∀ t : ℝ, ‖sawtoothWeight t‖ ≤ Real.exp (-t / 2)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), nativeLogForce φ = ∫ t, sawtoothWeight t * (deriv φ t - φ t / 2)) ∧
    (∀ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      nativeLogForce (hc.toSchwartzMap hφ) =
        ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
          ∫ t, (Real.exp (t / 2) : ℂ) * φ t) ∧
    (∀ n : ℕ, 1 ≤ n →
      Tendsto sawtoothWeight (𝓝[<] (Real.log n)) (𝓝 ((((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) ∧
        sawtoothWeight (Real.log n) = 0) := by
  refine ⟨integrable_sawtoothWeight, memLp_two_sawtoothWeight, fun t ht => sawtoothWeight_of_neg ht,
    norm_sawtoothWeight_le, nativeLogForce_apply, fun φ hφ hc => ?_, fun n hn => sawtooth_jump hn⟩
  rw [nativeLogForce_apply]
  exact sawtooth_compact_identity hφ hc

/-- F1: for 0 < Re s < 1, ∫_0^∞ {x} x^(-s-1) dx = -ζ(s)/s (derived from the Euler-Maclaurin
continuation, absolutely convergent); hence 𝓕_log w(ξ) = -ζ(1/2 + iξ)/(1/2 + iξ), the symbol
-(1/2 + iξ) of -(∂_t + 1/2) gives 𝓕_log 𝔤(ξ) = ζ(1/2 + iξ), and as tempered distributions
𝓕 𝔤 = ζ(1/2 + 2πi·) in the Mathlib convention (ξ = 2πη). -/
theorem sawtooth_actual_mellin_fourier :
    (∀ s : ℂ, 0 < s.re → s.re < 1 →
      IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = -riemannZeta s / s) ∧
    (∀ ξ : ℝ, logFourier sawtoothWeight ξ = -riemannZeta (1 / 2 + ξ * I) / (1 / 2 + ξ * I)) ∧
    (∀ ξ : ℝ, -(1 / 2 + ξ * I) * logFourier sawtoothWeight ξ = riemannZeta (1 / 2 + ξ * I)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 nativeLogForce) φ =
      ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * φ η) := by
  refine ⟨fun s h0 h1 => mellin_fract h0 h1, logFourier_sawtoothWeight, fun ξ => ?_,
    fourier_nativeLogForce⟩
  rw [logFourier_sawtoothWeight]
  have hne : (1 / 2 + (ξ : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [neg_div, neg_mul_neg, mul_comm, div_mul_cancel₀ _ hne]

/-- F1: the exact finite integer-cell norm identity (cells 1 and 1 + n/(n+1) - 2n log(1 + 1/n)),
its limit ‖w‖₂² = ∫_0^∞ {x}²/x² = log(2π) - γ, the weighted zeta moment
(1/2π) ∫ |ζ(1/2 + iξ)|²/(ξ² + 1/4) dξ = log(2π) - γ (absolutely convergent), and 𝔤 ∈ H⁻¹:
on H¹ tests |⟨𝔤, φ⟩| ≤ (log(2π) - γ)^(1/2) ‖φ‖_(H¹) with ‖φ‖²_(H¹) = ‖φ'‖² + ‖φ‖²/4. -/
theorem sawtooth_norm_weighted_zeta_moment :
    (∫ x in (0 : ℝ)..1, Int.fract x ^ 2 / x ^ 2) = 1 ∧
    (∀ n : ℕ, 1 ≤ n → ∫ x in (n : ℝ)..(n + 1), Int.fract x ^ 2 / x ^ 2 =
      1 + n / (n + 1) - 2 * n * Real.log (1 + 1 / n)) ∧
    (∀ L : ℕ, 1 ≤ L → ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2 =
      2 * L - harmonic L - 2 * (L - 1) * Real.log L + 2 * Real.log (Real.Gamma L)) ∧
    Tendsto (fun L : ℕ => ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2) atTop
      (𝓝 (Real.log (2 * π) - Real.eulerMascheroniConstant)) ∧
    (∫ t, ‖sawtoothWeight t‖ ^ 2) = Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    Integrable (fun ξ : ℝ => ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4)) ∧
    1 / (2 * π) * ∫ ξ : ℝ, ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4) =
      Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    (∀ φ φ' : ℝ → ℂ, LogH1 φ φ' →
      ‖∫ t, sawtoothWeight t * (φ' t - φ t / 2)‖ ≤
        (Real.log (2 * π) - Real.eulerMascheroniConstant) ^ (1 / 2 : ℝ) *
          ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), ‖nativeLogForce φ‖ ≤
        (Real.log (2 * π) - Real.eulerMascheroniConstant) ^ (1 / 2 : ℝ) *
          ((∫ t, ‖deriv φ t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hI, hN, hM⟩ := sawtooth_weighted_zeta_moment
  have hH : ∀ φ φ' : ℝ → ℂ, LogH1 φ φ' →
      ‖∫ t, sawtoothWeight t * (φ' t - φ t / 2)‖ ≤
        (Real.log (2 * π) - Real.eulerMascheroniConstant) ^ (1 / 2 : ℝ) *
          ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ) := fun φ φ' hφ => by
    rw [← hN]; exact (hφ.force_pairing_bound memLp_two_sawtoothWeight).2
  refine ⟨integral_fract_sq_zero, fun n hn => integral_fract_sq_cell hn,
    fun L hL => integral_fract_sq_closed hL, tendsto_integral_fract_sq, hN, hI, hM, hH,
    fun φ => ?_⟩
  rw [nativeLogForce_apply]
  exact hH φ (deriv φ) (logH1_schwartz φ)

end Roots

end Zeta23.OPICAFollowup
