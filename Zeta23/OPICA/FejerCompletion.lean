import Zeta23.CCM.NativePositiveCompletion
import Zeta23.OPICA.SincTriangle
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Zeta23.CCM.NativePositiveCompletionComplexLaplace
import Zeta23.OPICA.WeightedLaplace
import Mathlib.Analysis.Complex.Convex

/-!
# The convergent Fejer lattice sum and native completion

The actual positive-index sinc lattice sum is evaluated using Mathlib's
checked Fourier series for the second Bernoulli polynomial. This supplies
the exact floor formula, the native-completion comparison, and both cusp
derivatives. The Laplace comparison retains its rational additive term.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Zeta23.OPICA

open Zeta23.CCM

/-- The fractional part of `exp t`, with the native natural-floor convention. -/
def expFloorRemainder (t : ℝ) : ℝ := Real.exp t - ⌊Real.exp t⌋₊

/-- The causal floor expression in the last line of paper (10.3). Its
identification with the convergent lattice sum is proved below. -/
def fejerFloorKernel (t : ℝ) : ℝ :=
  if 0 ≤ t then
    expFloorRemainder t * (1 - expFloorRemainder t) * Real.exp (-(3 * t / 2))
  else 0

theorem expFloorRemainder_nonneg (t : ℝ) : 0 ≤ expFloorRemainder t := by
  exact sub_nonneg.mpr (Nat.floor_le (Real.exp_pos t).le)

theorem expFloorRemainder_lt_one (t : ℝ) : expFloorRemainder t < 1 := by
  unfold expFloorRemainder
  have := Nat.lt_floor_add_one (Real.exp t)
  linarith

theorem fejerFloorKernel_nonneg (t : ℝ) : 0 ≤ fejerFloorKernel t := by
  unfold fejerFloorKernel
  split_ifs with ht
  · exact mul_nonneg (mul_nonneg (expFloorRemainder_nonneg t)
      (sub_nonneg.mpr (expFloorRemainder_lt_one t).le)) (Real.exp_pos _).le
  · exact le_refl 0

theorem fejerFloorKernel_le_quarter_exp (t : ℝ) :
    fejerFloorKernel t ≤ (1 / 4 : ℝ) * Real.exp (-(3 * t / 2)) := by
  unfold fejerFloorKernel
  split_ifs with ht
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    nlinarith [sq_nonneg (expFloorRemainder t - 1 / 2)]
  · positivity

/-- The pointwise additive comparison uses the existing native completion. -/
theorem fejerFloorKernel_add_nativeCompletion {t : ℝ} (ht : 0 ≤ t) :
    fejerFloorKernel t + Zeta23.CCM.nativePositiveCompletion t =
      (1 - expFloorRemainder t) * Real.exp (-(t / 2)) := by
  have hexp : Real.exp t * Real.exp (-(3 * t / 2)) = Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [fejerFloorKernel, if_pos ht, Zeta23.CCM.nativePositiveCompletion, if_pos ht,
    ← hexp]
  unfold expFloorRemainder
  ring

/-- The floor index is nonzero on the causal half-line, so the ratio
in paper (10.4) has its ordinary, non-totalized meaning. -/
theorem expFloorIndex_pos {t : ℝ} (ht : 0 ≤ t) : 0 < ⌊Real.exp t⌋₊ := by
  have hexp : 1 ≤ Real.exp t := by simpa using Real.exp_le_exp.mpr ht
  exact Nat.zero_lt_one.trans_le ((Nat.one_le_floor_iff _).mpr hexp)

theorem fejerFloorKernel_eq_remainder_ratio_nativeCompletion {t : ℝ} (ht : 0 ≤ t) :
    fejerFloorKernel t =
      (expFloorRemainder t / (⌊Real.exp t⌋₊ : ℝ)) *
        Zeta23.CCM.nativePositiveCompletion t := by
  have hn : (⌊Real.exp t⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (expFloorIndex_pos ht))
  rw [fejerFloorKernel, if_pos ht, Zeta23.CCM.nativePositiveCompletion, if_pos ht]
  unfold expFloorRemainder
  field_simp <;> ring

theorem fejerFloorKernel_zero : fejerFloorKernel 0 = 0 := by
  norm_num [fejerFloorKernel, expFloorRemainder]

/-- The two finite floor expressions in paper (10.3) agree exactly. -/
theorem fejerFloorKernel_eq_expanded_floor {t : ℝ} (ht : 0 ≤ t) :
    fejerFloorKernel t =
      (2 * (⌊Real.exp t⌋₊ : ℝ) + 1) * Real.exp (-(t / 2)) -
        (⌊Real.exp t⌋₊ : ℝ) * ((⌊Real.exp t⌋₊ : ℝ) + 1) *
          Real.exp (-(3 * t / 2)) - Real.exp (t / 2) := by
  have hfirst : Real.exp (-(t / 2)) = Real.exp t * Real.exp (-(3 * t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsecond : Real.exp (t / 2) =
      Real.exp t * Real.exp t * Real.exp (-(3 * t / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [fejerFloorKernel, if_pos ht, hfirst, hsecond]
  unfold expFloorRemainder
  ring

/-- The actual positive-index sinc lattice sum. -/
def fejerLatticeKernel (t : ℝ) : ℝ :=
  2 * Real.exp (t / 2) *
    ∑' n : ℕ, sincSquared (((n + 1 : ℕ) : ℝ) * Real.exp t)

private theorem hasSum_sine_sq_div_nat_sq {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => Real.sin (Real.pi * n * u) ^ 2 / (n : ℝ) ^ 2)
      (Real.pi ^ 2 * u * (1 - u) / 2) := by
  have hcos : HasSum
      (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * u))
      (Real.pi ^ 2 * (u ^ 2 - u + 1 / 6)) := by
    have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hu
    change HasSum _ ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / (2 : ℕ).factorial *
      bernoulliFun 2 u) at h
    rw [bernoulliFun_two] at h
    norm_num at h
    convert! h using 1
    · funext n
      congr 2 <;> ring
    · ring
  have h := (hasSum_zeta_two.sub hcos).div_const 2
  convert! h using 1
  · funext n
    rw [Real.sin_sq_eq_half_sub]
    rw [show 2 * (Real.pi * (n : ℝ) * u) = 2 * Real.pi * n * u by ring]
    ring
  · ring

/-- The convergent positive sinc sum follows from Mathlib's proved Fourier
series for the second Bernoulli polynomial. Thus no nonsmooth Poisson
formula is introduced as a hypothesis. -/
theorem fejerLattice_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => sincSquared (((n + 1 : ℕ) : ℝ) * Real.exp t))
      (expFloorRemainder t * (1 - expFloorRemainder t) / (2 * Real.exp t ^ 2)) := by
  have hu : expFloorRemainder t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨expFloorRemainder_nonneg t, (expFloorRemainder_lt_one t).le⟩
  have hbase := hasSum_sine_sq_div_nat_sq hu
  have hshift : HasSum
      (fun n : ℕ => Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * expFloorRemainder t) ^ 2 /
        (((n + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 * expFloorRemainder t * (1 - expFloorRemainder t) / 2) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hbase
  have hperiod (n : ℕ) :
      Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * Real.exp t) ^ 2 =
        Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * expFloorRemainder t) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
    have hangle : 2 * (Real.pi * ((n + 1 : ℕ) : ℝ) * Real.exp t) =
        2 * (Real.pi * ((n + 1 : ℕ) : ℝ) * expFloorRemainder t) +
          (((n + 1) * ⌊Real.exp t⌋₊ : ℕ) : ℝ) * (2 * Real.pi) := by
      unfold expFloorRemainder
      push_cast
      ring
    rw [hangle, Real.cos_add_nat_mul_two_pi]
  have hdiv := hshift.div_const (Real.pi ^ 2 * Real.exp t ^ 2)
  convert! hdiv using 1
  · funext n
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have he : Real.exp t ≠ 0 := (Real.exp_pos _).ne'
    rw [sincSquared, Real.sinc_of_ne_zero
      (mul_ne_zero Real.pi_ne_zero (mul_ne_zero hn he))]
    rw [div_pow]
    rw [show Real.pi * (((n + 1 : ℕ) : ℝ) * Real.exp t) =
      Real.pi * ((n + 1 : ℕ) : ℝ) * Real.exp t by ring, hperiod]
    field_simp <;> ring
  · field_simp <;> ring

theorem fejerLatticeKernel_eq_floorKernel {t : ℝ} (ht : 0 ≤ t) :
    fejerLatticeKernel t = fejerFloorKernel t := by
  rw [fejerLatticeKernel, (fejerLattice_hasSum t).tsum_eq, fejerFloorKernel, if_pos ht]
  have he : Real.exp t ≠ 0 := (Real.exp_pos _).ne'
  have hexp : Real.exp (t / 2) = Real.exp (-(3 * t / 2)) * Real.exp t ^ 2 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp <;> ring

/-- H4's exact floor formula for the actual convergent sinc lattice sum. -/
theorem fejer_floor_formula {t : ℝ} (ht : 0 ≤ t) :
    fejerLatticeKernel t =
      (2 * (⌊Real.exp t⌋₊ : ℝ) + 1) * Real.exp (-(t / 2)) -
        (⌊Real.exp t⌋₊ : ℝ) * ((⌊Real.exp t⌋₊ : ℝ) + 1) *
          Real.exp (-(3 * t / 2)) - Real.exp (t / 2) := by
  rw [fejerLatticeKernel_eq_floorKernel ht, fejerFloorKernel_eq_expanded_floor ht]

/-- Both exact pointwise relations use the actual lattice sum and the
pre-existing native completion. -/
theorem fejer_nativeCompletion_pointwise {t : ℝ} (ht : 0 ≤ t) :
    fejerLatticeKernel t =
        (expFloorRemainder t / (⌊Real.exp t⌋₊ : ℝ)) *
          Zeta23.CCM.nativePositiveCompletion t ∧
      fejerLatticeKernel t + Zeta23.CCM.nativePositiveCompletion t =
        (1 - expFloorRemainder t) * Real.exp (-(t / 2)) ∧
      0 ≤ fejerLatticeKernel t ∧
      fejerLatticeKernel t ≤ (1 / 4 : ℝ) * Real.exp (-(3 * t / 2)) := by
  rw [fejerLatticeKernel_eq_floorKernel ht]
  exact ⟨fejerFloorKernel_eq_remainder_ratio_nativeCompletion ht,
    fejerFloorKernel_add_nativeCompletion ht, fejerFloorKernel_nonneg t,
    fejerFloorKernel_le_quarter_exp t⟩

private def fejerCellExpression (m t : ℝ) : ℝ :=
  (Real.exp t - m) * (m + 1 - Real.exp t) * Real.exp (-(3 * t / 2))

private theorem fejerFloorKernel_eq_cell {m : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hlow : (m : ℝ) ≤ Real.exp t) (hupper : Real.exp t ≤ (m : ℝ) + 1) :
    fejerFloorKernel t = fejerCellExpression (m : ℝ) t := by
  rcases lt_or_eq_of_le hupper with hlt | heq
  · have hfloor : ⌊Real.exp t⌋₊ = m :=
      (Nat.floor_eq_iff (Real.exp_pos t).le).mpr ⟨hlow, hlt⟩
    simp only [fejerFloorKernel, if_pos ht, expFloorRemainder, hfloor, fejerCellExpression]
    ring
  · have hfloor : ⌊Real.exp t⌋₊ = m + 1 := by
      apply (Nat.floor_eq_iff (Real.exp_pos t).le).mpr
      rw [heq]
      push_cast
      constructor <;> linarith
    simp only [fejerFloorKernel, if_pos ht, expFloorRemainder, hfloor, fejerCellExpression]
    push_cast
    rw [heq]
    ring

private theorem fejerCellExpression_hasDerivAt (m t : ℝ) :
    HasDerivAt (fejerCellExpression m)
      (Real.exp t * (m + 1 - Real.exp t) * Real.exp (-(3 * t / 2)) -
        (Real.exp t - m) * Real.exp t * Real.exp (-(3 * t / 2)) -
        3 / 2 * ((Real.exp t - m) * (m + 1 - Real.exp t)) * Real.exp (-(3 * t / 2))) t := by
  have hdecay : HasDerivAt (fun s : ℝ => Real.exp (-(3 * s / 2)))
      (-(3 / 2 : ℝ) * Real.exp (-(3 * t / 2))) t := by
    convert! ((hasDerivAt_id t).const_mul (-(3 / 2 : ℝ))).exp using 1 <;>
      simp only [id_eq] <;> ring
  convert! (((Real.hasDerivAt_exp t).sub_const m).mul
    ((Real.hasDerivAt_exp t).const_sub (m + 1))).mul hdecay using 1 <;>
    (try simp only [fejerCellExpression, id_eq, Pi.mul_apply]) <;> ring

private theorem fejer_cusp_scale {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.exp (-(3 * Real.log (n : ℝ) / 2)) = 1 / Real.sqrt (n : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = Real.exp (Real.log (n : ℝ)) * Real.exp (-(3 * Real.log (n : ℝ) / 2)) := by
      rw [Real.exp_log hnreal]
    _ = Real.exp (-(Real.log (n : ℝ) / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := by rw [Real.exp_neg, Real.exp_half, Real.exp_log hnreal, one_div]

/-- The right cell has the positive cusp slope. This is derived from the
actual convergent lattice sum through the checked floor identity. -/
theorem fejer_logInteger_rightDerivative {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt fejerLatticeKernel (1 / Real.sqrt (n : ℝ))
      (Set.Ici (Real.log (n : ℝ))) (Real.log (n : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hderiv := fejerCellExpression_hasDerivAt (n : ℝ) (Real.log (n : ℝ))
  have hderiv' : HasDerivAt (fejerCellExpression (n : ℝ))
      (1 / Real.sqrt (n : ℝ)) (Real.log (n : ℝ)) := by
    rw [← fejer_cusp_scale hnpos]
    convert! hderiv using 1
    rw [Real.exp_log hnreal]
    ring
  have hupper : ∀ᶠ t in nhds (Real.log (n : ℝ)), Real.exp t < (n : ℝ) + 1 := by
    exact (Real.continuous_exp.tendsto _).eventually
      (Iio_mem_nhds (by rw [Real.exp_log hnreal]; linarith))
  apply hderiv'.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [nhdsWithin_le_nhds hupper, self_mem_nhdsWithin] with t ht htle
    have htzero : 0 ≤ t := hlog.trans htle
    rw [fejerLatticeKernel_eq_floorKernel htzero]
    exact fejerFloorKernel_eq_cell htzero
      (by simpa only [Real.exp_log hnreal] using Real.exp_le_exp.mpr htle) ht.le
  · exact Set.mem_Ici.mpr le_rfl

/-- The left cell has the negative cusp slope. -/
theorem fejer_logInteger_leftDerivative {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt fejerLatticeKernel (-(1 / Real.sqrt (n : ℝ)))
      (Set.Iic (Real.log (n : ℝ))) (Real.log (n : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmone : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - 1 by omega)
  have hmcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hderiv := fejerCellExpression_hasDerivAt ((n - 1 : ℕ) : ℝ) (Real.log (n : ℝ))
  have hderiv' : HasDerivAt (fejerCellExpression ((n - 1 : ℕ) : ℝ))
      (-(1 / Real.sqrt (n : ℝ))) (Real.log (n : ℝ)) := by
    rw [← fejer_cusp_scale hnpos]
    convert! hderiv using 1
    rw [Real.exp_log hnreal, hmcast]
    ring
  have hlower : ∀ᶠ t in nhds (Real.log (n : ℝ)), ((n - 1 : ℕ) : ℝ) < Real.exp t := by
    exact (Real.continuous_exp.tendsto _).eventually
      (Ioi_mem_nhds (by rw [Real.exp_log hnreal, hmcast]; linarith))
  apply hderiv'.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [nhdsWithin_le_nhds hlower, self_mem_nhdsWithin] with t ht htle
    have htzero : 0 ≤ t := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_zero]
      exact hmone.trans ht.le
    rw [fejerLatticeKernel_eq_floorKernel htzero]
    apply fejerFloorKernel_eq_cell htzero ht.le
    have hbound := Real.exp_le_exp.mpr htle
    rw [Real.exp_log hnreal] at hbound
    rw [hmcast]
    linarith
  · exact Set.mem_Iic.mpr le_rfl

/-- H4: the actual lattice kernel has two distinct one-sided cusp slopes
at every logarithmic integer seam with index at least two. -/
theorem fejer_logInteger_oneSidedDerivatives {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt fejerLatticeKernel (-(1 / Real.sqrt (n : ℝ)))
        (Set.Iic (Real.log (n : ℝ))) (Real.log (n : ℝ)) ∧
      HasDerivWithinAt fejerLatticeKernel (1 / Real.sqrt (n : ℝ))
        (Set.Ici (Real.log (n : ℝ))) (Real.log (n : ℝ)) :=
  ⟨fejer_logInteger_leftDerivative hn, fejer_logInteger_rightDerivative hn⟩

private def fejerCausalExp (a t : ℝ) : ℝ := if 0 ≤ t then Real.exp (a * t) else 0

private theorem fejerCausalExp_zero_of_neg (a : ℝ) {t : ℝ} (ht : t < 0) :
    fejerCausalExp a t = 0 := by simp [fejerCausalExp, not_le.mpr ht]

private theorem fejerCausalExp_damped_eq (a : ℝ) (w : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ) =
      Complex.exp (-(w - (a : ℂ)) * (t : ℂ)) := by
  simp only [fejerCausalExp, if_pos ht, Complex.ofReal_exp, Complex.ofReal_mul]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem fejerCausalExp_damped_integrable (a : ℝ) {w : ℂ} (hw : a < w.re) :
    Integrable (fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ)) := by
  have hneg : (-(w - (a : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
    linarith
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  constructor
  · have hz : EqOn (fun _ : ℝ => (0 : ℂ))
        (fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ)) (Iio 0) := by
      intro t ht
      change (0 : ℂ) = Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ)
      rw [fejerCausalExp_zero_of_neg a ht]
      simp
    exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Iio 0)).congr_fun
      hz measurableSet_Iio
  · exact (integrableOn_exp_mul_complex_Ioi hneg 0).congr_fun
      (fun t ht => (fejerCausalExp_damped_eq a w ht.le).symm) measurableSet_Ioi

private theorem fejerCausalExp_complexLaplace (a : ℝ) {w : ℂ} (hw : a < w.re) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ)) =
      1 / (w - (a : ℂ)) := by
  have hs : (∫ t : ℝ in Ici 0, Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ)) =
      ∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [fejerCausalExp_zero_of_neg a (lt_of_not_ge ht)]
    simp
  rw [← hs, integral_Ici_eq_integral_Ioi]
  have hneg : (-(w - (a : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
    linarith
  have heq : (fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (fejerCausalExp a t : ℂ)) =ᵐ[
      volume.restrict (Ioi 0)] (fun t : ℝ => Complex.exp (-(w - (a : ℂ)) * (t : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact fejerCausalExp_damped_eq a w ht.le
  rw [integral_congr_ae heq, integral_exp_mul_complex_Ioi hneg]
  simp
  rw [show (a : ℂ) - w = -(w - (a : ℂ)) by ring]
  rw [neg_div_neg_eq, one_div]

private theorem fejerCausalExp_integerAction (t : ℝ) :
    nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ))) t =
      if 0 ≤ t then (⌊Real.exp t⌋₊ : ℝ) * Real.exp (-(t / 2)) else 0 := by
  rw [nativeIntegerTranslateAction_eq_causal_history
    (fun s hs => fejerCausalExp_zero_of_neg _ hs) t]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, Finset.sum_range_succ']
    have hzero : nativeIntegerCoefficient 0 * fejerCausalExp (-(1 / 2 : ℝ))
        (t - Real.log ((0 : ℕ) : ℝ)) = 0 := by simp [nativeIntegerCoefficient]
    rw [hzero, add_zero]
    have hsum : (∑ n ∈ Finset.range ⌊Real.exp t⌋₊,
        nativeIntegerCoefficient (n + 1) * fejerCausalExp (-(1 / 2 : ℝ))
          (t - Real.log (((n + 1 : ℕ) : ℝ)))) =
        ∑ _n ∈ Finset.range ⌊Real.exp t⌋₊, Real.exp (-(t / 2)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have hroot : Real.sqrt (((n + 1 : ℕ) : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
      have hcast : (((n + 1 : ℕ) : ℝ)) ≤ (⌊Real.exp t⌋₊ : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
      have hlog : Real.log (((n + 1 : ℕ) : ℝ)) ≤ t :=
        (Real.log_le_iff_le_exp hnpos).mpr (hcast.trans (Nat.floor_le (Real.exp_pos t).le))
      have hexp : Real.exp (-(1 / 2 : ℝ) * (t - Real.log (((n + 1 : ℕ) : ℝ)))) =
          Real.exp (-(t / 2)) * Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
        rw [show -(1 / 2 : ℝ) * (t - Real.log (((n + 1 : ℕ) : ℝ))) =
          -(t / 2) + Real.log (((n + 1 : ℕ) : ℝ)) / 2 by ring,
          Real.exp_add, Real.exp_half, Real.exp_log hnpos]
      rw [fejerCausalExp, if_pos (sub_nonneg.mpr hlog), hexp, nativeIntegerCoefficient]
      field_simp
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · have hfloor : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (lt_of_not_ge ht))
    simp [if_neg ht, hfloor, nativeIntegerCoefficient]

private theorem fejerFloorKernel_integerAction_identity (t : ℝ) :
    fejerFloorKernel t =
      nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ))) t +
        fejerCausalExp (-(1 / 2 : ℝ)) t - fejerCausalExp (1 / 2 : ℝ) t -
        nativePositiveCompletion t := by
  rw [fejerCausalExp_integerAction]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, fejerFloorKernel_eq_expanded_floor ht]
    simp only [fejerCausalExp, if_pos ht, nativePositiveCompletion]
    have hexp : Real.exp (-(t / 2)) = Real.exp (-(3 * t / 2)) * Real.exp t := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show -(1 / 2 : ℝ) * t = -(t / 2) by ring,
      show (1 / 2 : ℝ) * t = t / 2 by ring, hexp]
    ring
  · simp [fejerFloorKernel, ht, fejerCausalExp, nativePositiveCompletion_eq_zero_of_neg (lt_of_not_ge ht)]

private theorem fejer_integerAction_complexLaplace {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) *
      (nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ))) t : ℂ)) =
        riemannZeta (w + 1 / 2) / (w + 1 / 2) := by
  let g := fejerCausalExp (-(1 / 2 : ℝ))
  let b := fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (g t : ℂ)
  let term := fun n : ℕ => fun t : ℝ => Complex.exp (-w * (t : ℂ)) *
    (nativeIntegerCoefficient n * g (t - Real.log n) : ℝ)
  have hb : Integrable b := fejerCausalExp_damped_integrable _ (by linarith)
  have hfactor (n : ℕ) (t : ℝ) : term n t = nativeIntegerLaplaceCoefficient w n * b (t - Real.log n) := by
    have hexp : Complex.exp (-w * (t : ℂ)) =
        Complex.exp (-w * (Real.log n : ℂ)) * Complex.exp (-w * ((t - Real.log n : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [term, b, nativeIntegerLaplaceCoefficient, Complex.ofReal_mul]
    rw [hexp]
    ring
  have hterm (n : ℕ) : Integrable (term n) :=
    ((hb.comp_sub_right (Real.log n)).const_mul (nativeIntegerLaplaceCoefficient w n)).congr
      (Eventually.of_forall (fun t => (hfactor n t).symm))
  have hnorm (n : ℕ) : (∫ t : ℝ, ‖term n t‖) =
      ‖nativeIntegerLaplaceCoefficient w n‖ * ∫ t : ℝ, ‖b t‖ := by
    simp_rw [hfactor, norm_mul]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun t : ℝ => ‖b t‖) (Real.log n)
  have hnormsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖term n t‖) := by
    simp_rw [hnorm]
    exact (nativeIntegerLaplaceCoefficient_summable_norm hw).mul_right _
  have hint (n : ℕ) : (∫ t : ℝ, term n t) = nativeIntegerLaplaceCoefficient w n * ∫ t : ℝ, b t := by
    simp_rw [hfactor]
    rw [integral_const_mul, integral_sub_right_eq_self]
  have hsum := hasSum_integral_of_summable_integral_norm hterm hnormsum
  have hpoint (t : ℝ) : Complex.exp (-w * (t : ℂ)) *
      (nativeIntegerTranslateAction g t : ℂ) = ∑' n : ℕ, term n t := by
    simp only [nativeIntegerTranslateAction, Complex.ofReal_tsum]
    rw [← tsum_mul_left]
  calc
    _ = ∫ t : ℝ, ∑' n : ℕ, term n t := integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∑' n : ℕ, ∫ t : ℝ, term n t := hsum.tsum_eq.symm
    _ = (∑' n : ℕ, nativeIntegerLaplaceCoefficient w n) * ∫ t : ℝ, b t := by
      simp_rw [hint]
      rw [tsum_mul_right]
    _ = _ := by
      rw [nativeIntegerLaplaceCoefficient_tsum hw]
      have hg := fejerCausalExp_complexLaplace (-(1 / 2 : ℝ)) (w := w) (by linarith)
      change (∫ t : ℝ, b t) = _ at hg
      rw [hg]
      norm_num <;> ring

/-- The actual causal Laplace transform of the lattice kernel. -/
def fejerLaplace (w : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-w * (t : ℂ)) * (fejerLatticeKernel t : ℂ)

private theorem fejer_integerAction_damped_integrable {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun t : ℝ => Complex.exp (-w * (t : ℂ)) *
      (nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ))) t : ℂ)) := by
  have hact : Measurable (nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ)))) := by
    have heq : nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ))) =
        (Ici (0 : ℝ)).indicator (fun t : ℝ => (⌊Real.exp t⌋₊ : ℝ) * Real.exp (-(t / 2))) := by
      funext t
      rw [fejerCausalExp_integerAction]
      by_cases ht : 0 ≤ t <;> simp [ht]
    rw [heq]
    apply Measurable.indicator _ measurableSet_Ici
    fun_prop
  have hm : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-w * (t : ℂ)) *
      (nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ))) t : ℂ)) volume := by
    fun_prop
  apply (fejerCausalExp_damped_integrable (1 / 2) hw).norm.mono' hm
  filter_upwards with t
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    fejerCausalExp_integerAction]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, fejerCausalExp, if_pos ht, abs_of_nonneg (mul_nonneg
      (Nat.cast_nonneg _) (Real.exp_pos _).le), abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp t * Real.exp (-(t / 2)) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (Real.exp_pos t).le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · simp [fejerCausalExp, ht]

theorem fejerLaplace_eq_floorLaplace (w : ℂ) :
    fejerLaplace w = ∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (fejerFloorKernel t : ℂ) := by
  have heq : (fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (fejerLatticeKernel t : ℂ)) =ᵐ[
      volume.restrict (Ioi 0)] (fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (fejerFloorKernel t : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [fejerLatticeKernel_eq_floorKernel ht.le]
  rw [fejerLaplace, integral_congr_ae heq, ← integral_Ici_eq_integral_Ioi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [fejerFloorKernel, show ¬ 0 ≤ t from ht]

private theorem fejerLaplace_safe_formula {w : ℂ} (hw : 1 / 2 < w.re) :
    fejerLaplace w = riemannZeta (w + 1 / 2) / (w + 1 / 2) +
      1 / (w + 1 / 2) - 1 / (w - 1 / 2) - nativePositiveCompletionLaplace w := by
  have hact := fejer_integerAction_damped_integrable hw
  have hminus := fejerCausalExp_damped_integrable (-(1 / 2 : ℝ)) (w := w) (by linarith)
  have hplus := fejerCausalExp_damped_integrable (1 / 2 : ℝ) hw
  have ha : Integrable (fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (nativePositiveCompletion t : ℂ)) :=
    nativeCausalComplexDamping_integrable (by linarith) nativePositiveCompletion_integrable
      (fun t ht => nativePositiveCompletion_eq_zero_of_neg ht)
  have heq : (fun t : ℝ => Complex.exp (-w * (t : ℂ)) * (fejerFloorKernel t : ℂ)) =
      fun t : ℝ => (Complex.exp (-w * (t : ℂ)) *
          (nativeIntegerTranslateAction (fejerCausalExp (-(1 / 2 : ℝ))) t : ℂ) +
        Complex.exp (-w * (t : ℂ)) * (fejerCausalExp (-(1 / 2 : ℝ)) t : ℂ) -
        Complex.exp (-w * (t : ℂ)) * (fejerCausalExp (1 / 2 : ℝ) t : ℂ)) -
        Complex.exp (-w * (t : ℂ)) * (nativePositiveCompletion t : ℂ) := by
    funext t
    rw [fejerFloorKernel_integerAction_identity]
    push_cast
    ring
  have hout := integral_sub ((hact.add hminus).sub hplus) ha
  have hinner := integral_sub (hact.add hminus) hplus
  simp only [Pi.sub_apply, Pi.add_apply] at hout hinner
  rw [fejerLaplace_eq_floorLaplace, heq, hout, hinner, integral_add hact hminus,
    fejer_integerAction_complexLaplace hw,
    fejerCausalExp_complexLaplace (-(1 / 2 : ℝ)) (by linarith),
    fejerCausalExp_complexLaplace (1 / 2 : ℝ) hw]
  norm_num [nativePositiveCompletionLaplace]

/-- The affine relation is first established on the common half-plane of
absolute convergence of the integer expansion. The rational correction is
part of the conclusion, rather than discarded as a multiplicative unit. -/
theorem fejer_completion_affine_identity_of_half_lt_re {w : ℂ} (hw : 1 / 2 < w.re) :
    nativePositiveCompletionLaplace w =
      (1 / 2 : ℂ) * (w - 1 / 2) * fejerLaplace w + 1 / (2 * (w + 1 / 2)) := by
  have hne : w ≠ 1 / 2 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hplus : w + 1 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hthree : w + 3 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hminus : w - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
  have ha : nativePositiveCompletionLaplace w =
      nativeCompletionRationalMultiplier w * riemannZeta (w + 1 / 2) :=
    nativePositiveCompletion_complexLaplace (by linarith) hne
  rw [fejerLaplace_safe_formula hw]
  simp only [ha, nativeCompletionRationalMultiplier]
  have hrelplus : w + (1 / 2 : ℂ) = (w - 1 / 2) + 1 := by ring
  have hrelthree : w + (3 / 2 : ℂ) = (w - 1 / 2) + 2 := by ring
  generalize hpx : w + (1 / 2 : ℂ) = p at *
  generalize hmx : w - (1 / 2 : ℂ) = q at *
  generalize htx : w + (3 / 2 : ℂ) = r at *
  field_simp [hplus, hminus, hthree]
  rw [hrelplus, hrelthree]
  ring

private theorem fejerFloorKernel_measurable : Measurable fejerFloorKernel := by
  have hf : Measurable (fun t : ℝ =>
      expFloorRemainder t * (1 - expFloorRemainder t) * Real.exp (-(3 * t / 2))) := by
    unfold expFloorRemainder
    fun_prop
  have heq : fejerFloorKernel = (Ici (0 : ℝ)).indicator
      (fun t : ℝ => expFloorRemainder t * (1 - expFloorRemainder t) * Real.exp (-(3 * t / 2))) := by
    funext t
    by_cases ht : 0 ≤ t <;> simp [fejerFloorKernel, ht]
  rw [heq]
  exact hf.indicator measurableSet_Ici

private theorem fejerFloorKernel_le_exp_half {t : ℝ} (ht : 0 ≤ t) :
    fejerFloorKernel t ≤ Real.exp (-(t / 2)) := by
  have h := fejerFloorKernel_add_nativeCompletion ht
  have hu := expFloorRemainder_nonneg t
  have ha := nativePositiveCompletion_nonneg t
  have hp := Real.exp_pos (-(t / 2))
  nlinarith [mul_nonneg hu hp.le]

private theorem fejer_weighted_memLp_of_half_decay {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ Real.exp (-(t / 2)))
    {epsilon : ℝ} (hepsilon : -(1 / 2 : ℝ) < epsilon) :
    MemLp (weightedCausalProfile epsilon (fun t => (f t : ℂ))) 2 volume := by
  have hw : 0 < ((epsilon + 1 / 2 : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hmajorant := nativeCausalExponentialPolynomial_memLp hw 0
  have hm : AEStronglyMeasurable (weightedCausalProfile epsilon (fun t => (f t : ℂ))) volume := by
    unfold weightedCausalProfile
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Ici
    fun_prop
  apply hmajorant.mono hm
  filter_upwards with t
  by_cases ht : 0 ≤ t
  · rw [weightedCausalProfile, indicator_of_mem (show t ∈ Ici 0 from ht), norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs, nativeCausalExponentialPolynomial_norm _ 0 ht,
      pow_zero, one_mul]
    have hre : (-((epsilon : ℂ)) * (t : ℂ)).re = -epsilon * t := by simp
    rw [hre, Complex.ofReal_re]
    calc
      _ ≤ Real.exp (-epsilon * t) * Real.exp (-(t / 2)) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · rw [weightedCausalProfile, indicator_of_notMem (show t ∉ Ici 0 from ht),
      nativeCausalExponentialPolynomial_zero_of_neg _ 0 (lt_of_not_ge ht)]

private theorem nativeCompletionLaplace_analyticAt_full {w : ℂ} (hw : -(1 / 2 : ℝ) < w.re) :
    AnalyticAt ℂ nativePositiveCompletionLaplace w := by
  let epsilon : ℝ := (w.re - 1 / 2) / 2
  have hepsilon : -(1 / 2 : ℝ) < epsilon := by dsimp [epsilon]; linarith
  have hepsilonw : epsilon < w.re := by dsimp [epsilon]; linarith
  let data : WeightedL2Data := {
    source := fun t => (nativePositiveCompletion t : ℂ)
    epsilon := epsilon
    weighted_memLp := fejer_weighted_memLp_of_half_decay nativePositiveCompletion_measurable
      (fun t _ => by
        rw [abs_of_nonneg (nativePositiveCompletion_nonneg t)]
        exact nativePositiveCompletion_le_exp t) hepsilon }
  have heq : weightedLaplace data = nativePositiveCompletionLaplace := by
    funext z
    change (∫ t : ℝ in Ici 0, Complex.exp (-z * (t : ℂ)) * (nativePositiveCompletion t : ℂ)) = _
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [nativePositiveCompletion_eq_zero_of_neg (lt_of_not_ge ht)]
    simp
  have h := laplace_holomorphic_of_weighted_L2 data w hepsilonw
  rw [heq] at h
  exact h

private theorem fejer_weighted_memLp_of_decay (decay : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f)
    (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ Real.exp (-(decay * t)))
    {epsilon : ℝ} (hepsilon : -decay < epsilon) :
    MemLp (weightedCausalProfile epsilon (fun t => (f t : ℂ))) 2 volume := by
  have hw : 0 < ((epsilon + decay : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hmajorant := nativeCausalExponentialPolynomial_memLp hw 0
  have hm : AEStronglyMeasurable (weightedCausalProfile epsilon (fun t => (f t : ℂ))) volume := by
    unfold weightedCausalProfile
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Ici
    fun_prop
  apply hmajorant.mono hm
  filter_upwards with t
  by_cases ht : 0 ≤ t
  · rw [weightedCausalProfile, indicator_of_mem (show t ∈ Ici 0 from ht), norm_mul,
      Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      nativeCausalExponentialPolynomial_norm _ 0 ht, pow_zero, one_mul]
    have hre : (-((epsilon : ℂ)) * (t : ℂ)).re = -epsilon * t := by simp
    rw [hre, Complex.ofReal_re]
    calc
      _ ≤ Real.exp (-epsilon * t) * Real.exp (-(decay * t)) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · rw [weightedCausalProfile, indicator_of_notMem (show t ∉ Ici 0 from ht),
      nativeCausalExponentialPolynomial_zero_of_neg _ 0 (lt_of_not_ge ht)]

/-- The lattice kernel's own sharp decay gives its full actual Laplace
strip. The affine comparison with the native completion uses the smaller
intersection of their convergence domains. -/
theorem fejerLaplace_analyticAt_fullStrip {w : ℂ} (hw : -(3 / 2 : ℝ) < w.re) :
    AnalyticAt ℂ fejerLaplace w := by
  let epsilon : ℝ := (w.re - 3 / 2) / 2
  have hepsilon : -(3 / 2 : ℝ) < epsilon := by dsimp [epsilon]; linarith
  have hepsilonw : epsilon < w.re := by dsimp [epsilon]; linarith
  let data : WeightedL2Data := {
    source := fun t => (fejerFloorKernel t : ℂ)
    epsilon := epsilon
    weighted_memLp := fejer_weighted_memLp_of_decay (3 / 2) fejerFloorKernel_measurable
      (fun t _ht => by
        rw [abs_of_nonneg (fejerFloorKernel_nonneg t)]
        calc
          fejerFloorKernel t ≤ (1 / 4 : ℝ) * Real.exp (-(3 * t / 2)) :=
            fejerFloorKernel_le_quarter_exp t
          _ ≤ Real.exp (-(3 * t / 2)) := by nlinarith [Real.exp_pos (-(3 * t / 2))]
          _ = Real.exp (-((3 / 2 : ℝ) * t)) := by congr 1; ring) hepsilon }
  have heq : weightedLaplace data = fejerLaplace := by
    funext z
    rw [fejerLaplace_eq_floorLaplace]
    change (∫ t : ℝ in Ici 0, Complex.exp (-z * (t : ℂ)) * (fejerFloorKernel t : ℂ)) = _
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp [fejerFloorKernel, show ¬ 0 ≤ t from ht]
  have h := laplace_holomorphic_of_weighted_L2 data w hepsilonw
  rw [heq] at h
  exact h

theorem fejerLaplace_analyticAt {w : ℂ} (hw : -(1 / 2 : ℝ) < w.re) :
    AnalyticAt ℂ fejerLaplace w := by
  let epsilon : ℝ := (w.re - 1 / 2) / 2
  have hepsilon : -(1 / 2 : ℝ) < epsilon := by dsimp [epsilon]; linarith
  have hepsilonw : epsilon < w.re := by dsimp [epsilon]; linarith
  let data : WeightedL2Data := {
    source := fun t => (fejerFloorKernel t : ℂ)
    epsilon := epsilon
    weighted_memLp := fejer_weighted_memLp_of_half_decay fejerFloorKernel_measurable
      (fun t ht => by
        rw [abs_of_nonneg (fejerFloorKernel_nonneg t)]
        exact fejerFloorKernel_le_exp_half ht) hepsilon }
  have heq : weightedLaplace data = fejerLaplace := by
    funext z
    rw [fejerLaplace_eq_floorLaplace]
    change (∫ t : ℝ in Ici 0, Complex.exp (-z * (t : ℂ)) * (fejerFloorKernel t : ℂ)) = _
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp [fejerFloorKernel, show ¬ 0 ≤ t from ht]
  have h := laplace_holomorphic_of_weighted_L2 data w hepsilonw
  rw [heq] at h
  exact h

/-- H4's exact affine identity on the common actual Laplace domain. In
particular the removable point `w=1/2` is included. Holomorphic continuation
is applied to actual integrals, after the norm-summable safe-domain proof. -/
theorem fejer_completion_affine_identity {w : ℂ} (hw : -(1 / 2 : ℝ) < w.re) :
    nativePositiveCompletionLaplace w =
      (1 / 2 : ℂ) * (w - 1 / 2) * fejerLaplace w + 1 / (2 * (w + 1 / 2)) := by
  let D : Set ℂ := {z : ℂ | -(1 / 2 : ℝ) < z.re}
  have hf : AnalyticOnNhd ℂ nativePositiveCompletionLaplace D :=
    fun z hz => nativeCompletionLaplace_analyticAt_full hz
  have hg : AnalyticOnNhd ℂ
      (fun z : ℂ => (1 / 2 : ℂ) * (z - 1 / 2) * fejerLaplace z + 1 / (2 * (z + 1 / 2))) D := by
    intro z hz
    have hplus : z + 1 / 2 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      change -(1 / 2 : ℝ) < z.re at hz
      linarith
    exact ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).mul
      (fejerLaplace_analyticAt hz)).add
        (analyticAt_const.div (analyticAt_const.mul (analyticAt_id.add analyticAt_const))
          (mul_ne_zero (by norm_num) hplus))
  have hlocal : nativePositiveCompletionLaplace =ᶠ[nhds (1 : ℂ)]
      (fun z : ℂ => (1 / 2 : ℂ) * (z - 1 / 2) * fejerLaplace z + 1 / (2 * (z + 1 / 2))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)] with z hz
    exact fejer_completion_affine_identity_of_half_lt_re hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt (-(1 / 2 : ℝ))).isPreconnected
      (by norm_num [D]) hlocal hw

end Zeta23.OPICA

#print axioms Zeta23.OPICA.fejerFloorKernel_add_nativeCompletion
#print axioms Zeta23.OPICA.fejerFloorKernel_eq_remainder_ratio_nativeCompletion
#print axioms Zeta23.OPICA.fejer_floor_formula
#print axioms Zeta23.OPICA.fejer_nativeCompletion_pointwise
#print axioms Zeta23.OPICA.fejer_logInteger_oneSidedDerivatives
