import Zeta23.CCM.UniversalSincSourceFacade
import Zeta23.CCM.UniversalSincInverseGevreyBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual source scaling and the three-term physical pole-killed energy. -/

noncomputable section

open Set MeasureTheory Complex
open scoped Topology

namespace Zeta23.CCM

theorem universalSincProduct_scale (s : ℝ) (z : ℂ) :
    UniversalSinc.product s z = UniversalSinc.product 1 ((s : ℂ) * z) := by
  unfold UniversalSinc.product
  apply tprod_congr
  intro n
  congr 1
  unfold UniversalSinc.width
  push_cast
  ring

theorem universalSincSource_complex_scale {s : ℝ} (hs : 0 < s) (x : ℝ) :
    UniversalSinc.originalDensityComplex s x =
      ((s⁻¹ : ℝ) : ℂ) * UniversalSinc.originalDensityComplex 1 (x / s) := by
  rw [← UniversalSinc.inverseCandidate_eq_originalDensityComplex hs,
    ← UniversalSinc.inverseCandidate_eq_originalDensityComplex (by norm_num : (0 : ℝ) < 1)]
  let g : ℝ → ℂ := fun ξ => UniversalSinc.product 1 (ξ : ℂ) *
    Complex.exp (I * ((-(x / s) : ℝ) : ℂ) * (ξ : ℂ))
  have hi : (∫ ξ : ℝ, UniversalSinc.product s (ξ : ℂ) *
      Complex.exp (I * ((-x : ℝ) : ℂ) * (ξ : ℂ))) = ∫ ξ : ℝ, g (s * ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [universalSincProduct_scale]
    dsimp [g]
    push_cast
    congr 1
    congr 1
    field_simp [hs.ne'] <;> ring
  unfold UniversalSinc.inverseCandidate
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def, hi, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr hs), RCLike.real_smul_eq_coe_mul]
  dsimp [g]
  push_cast
  ring

theorem universalSincSource_scale {s : ℝ} (hs : 0 < s) (x : ℝ) :
    universalSincSource s x = s⁻¹ * universalSincSource 1 (x / s) := by
  have hh := congrArg Complex.re (universalSincSource_complex_scale hs x)
  simpa only [UniversalSinc.originalDensityComplex, universalSincSource,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hh

private theorem source_jet_contDiff (s : ℝ) (hs : 0 < s) (r : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv r (universalSincSource s)) := by
  induction r with
  | zero => exact universalSincSource_contDiff hs
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem universalSincSource_iteratedDeriv_scale {s : ℝ} (hs : 0 < s) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (universalSincSource s) x =
      (s⁻¹) ^ (r + 1) * iteratedDeriv r (universalSincSource 1) (x / s) := by
  have he : universalSincSource s = fun y => s⁻¹ * universalSincSource 1 (s⁻¹ * y) := by
    funext y
    simpa only [div_eq_mul_inv, mul_comm] using universalSincSource_scale hs y
  have hf : ContDiff ℝ r (universalSincSource 1) :=
    (universalSincSource_contDiff (by norm_num : (0 : ℝ) < 1)).of_le (by
      exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul hf]
  simp only [div_eq_mul_inv, pow_succ]
  rw [mul_comm x s⁻¹]
  ring

theorem universalSincSource_iteratedDeriv_energy_scale {s : ℝ} (hs : 0 < s) (r : ℕ) :
    (∫ x : ℝ, (iteratedDeriv r (universalSincSource s) x) ^ 2) =
      (s ^ (2 * r + 1))⁻¹ * ∫ x : ℝ, (iteratedDeriv r (universalSincSource 1) x) ^ 2 := by
  simp_rw [universalSincSource_iteratedDeriv_scale hs, mul_pow]
  rw [integral_const_mul]
  rw [Measure.integral_comp_div (fun y => (iteratedDeriv r (universalSincSource 1) y) ^ 2) s,
    abs_of_pos hs, smul_eq_mul]
  have hc : ((s⁻¹) ^ (r + 1)) ^ 2 * s = (s ^ (2 * r + 1))⁻¹ := by
    have hp : (s⁻¹) ^ (r + 1) = (s ^ r)⁻¹ * s⁻¹ := by rw [pow_succ, inv_pow]
    calc
      _ = ((s ^ r)⁻¹ * s⁻¹) ^ 2 * s := by rw [hp]
      _ = ((s ^ r) ^ 2 * s)⁻¹ := by
        field_simp [hs.ne', pow_ne_zero r hs.ne']
        <;> ring
      _ = _ := by
        congr 1
        conv_rhs => rw [show 2 * r + 1 = r * 2 + 1 by omega, pow_succ, pow_mul]
  rw [← mul_assoc, hc]

private theorem real_deriv_complex (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    deriv (fun x => (f x : ℂ)) = fun x => ((deriv f x : ℝ) : ℂ) := by
  funext x
  exact ((hf x).hasDerivAt.ofReal_comp).deriv

private theorem real_iteratedDeriv_complex (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℕ) :
    iteratedDeriv r (fun x => (f x : ℂ)) = fun x => ((iteratedDeriv r f x : ℝ) : ℂ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    simpa only [iteratedDeriv_succ] using real_deriv_complex _ (hf.differentiable_iteratedDeriv r (by
      exact_mod_cast (show (r : ℕ∞) < ⊤ from WithTop.coe_lt_top r)))

theorem universalSincKernel_eq_real (s : ℝ) (hs : 0 < s) (x : ℝ) :
    universalSincKernel s x =
      ((deriv (deriv (universalSincSource s)) x - (1 / 4 : ℝ) * universalSincSource s x : ℝ) : ℂ) := by
  have hq := (universalSincSource_contDiff hs).differentiable (by norm_num)
  have hd := (source_jet_contDiff s hs 1).differentiable (by norm_num)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hd
  change deriv (deriv (fun y => (universalSincSource s y : ℂ))) x -
    (1 / 4 : ℂ) * (universalSincSource s x : ℂ) = _
  rw [real_deriv_complex _ hq, real_deriv_complex _ hd]
  push_cast
  rfl

private theorem source_jet_compact (s : ℝ) (hs : 0 < s) (r : ℕ) :
    HasCompactSupport (iteratedDeriv r (universalSincSource s)) := by
  have hq : HasCompactSupport (universalSincSource s) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (universalSincSource_support hs)
  induction r with
  | zero => exact hq
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv

private theorem real_source_kernel_energy (s : ℝ) (hs : 0 < s) :
    (∫ x : ℝ, ‖universalSincKernel s x‖ ^ 2) =
      (∫ x : ℝ, (deriv (deriv (universalSincSource s)) x) ^ 2) +
        (1 / 2 : ℝ) * (∫ x : ℝ, (deriv (universalSincSource s) x) ^ 2) +
        (1 / 16 : ℝ) * (∫ x : ℝ, (universalSincSource s x) ^ 2) := by
  let q := universalSincSource s
  have hq := (universalSincSource_contDiff hs).differentiable (by norm_num)
  have hd := (source_jet_contDiff s hs 1).differentiable (by norm_num)
  have hc0 := (source_jet_contDiff s hs 0).continuous
  have hc1 := (source_jet_contDiff s hs 1).continuous
  have hc2 := (source_jet_contDiff s hs 2).continuous
  have hs0 := source_jet_compact s hs 0
  have hs1 := source_jet_compact s hs 1
  have hs2 := source_jet_compact s hs 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hd hc0 hc1 hc2 hs0 hs1 hs2
  have hi0 : Integrable (fun x => q x * q x) volume :=
    (hc0.mul hc0).integrable_of_hasCompactSupport hs0.mul_right
  have hi1 : Integrable (fun x => deriv q x * deriv q x) volume :=
    (hc1.mul hc1).integrable_of_hasCompactSupport hs1.mul_right
  have hi2 : Integrable (fun x => deriv (deriv q) x * deriv (deriv q) x) volume :=
    (hc2.mul hc2).integrable_of_hasCompactSupport hs2.mul_right
  have hi02 : Integrable (fun x => q x * deriv (deriv q) x) volume :=
    (hc0.mul hc2).integrable_of_hasCompactSupport hs0.mul_right
  have hi01 : Integrable (fun x => q x * deriv q x) volume :=
    (hc0.mul hc1).integrable_of_hasCompactSupport hs0.mul_right
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := q) (v := deriv q) (u' := deriv q) (v' := deriv (deriv q))
    (fun x _ => (hq x).hasDerivAt) (fun x _ => (hd x).hasDerivAt) hi02 hi1 hi01
  simp_rw [universalSincKernel_eq_real s hs, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change (∫ x : ℝ, (deriv (deriv q) x - (1 / 4 : ℝ) * q x) ^ 2) = _
  have he (x : ℝ) : (deriv (deriv q) x - (1 / 4 : ℝ) * q x) ^ 2 =
      (deriv (deriv q) x * deriv (deriv q) x) - (1 / 2 : ℝ) * (q x * deriv (deriv q) x) +
        (1 / 16 : ℝ) * (q x * q x) := by ring
  simp_rw [he]
  have hsplit :
      (∫ x : ℝ, deriv (deriv q) x * deriv (deriv q) x - (1 / 2 : ℝ) * (q x * deriv (deriv q) x) +
        (1 / 16 : ℝ) * (q x * q x)) =
      ((∫ x : ℝ, deriv (deriv q) x * deriv (deriv q) x) -
        (1 / 2 : ℝ) * ∫ x : ℝ, q x * deriv (deriv q) x) +
        (1 / 16 : ℝ) * ∫ x : ℝ, q x * q x := by
    calc
      _ = (∫ x : ℝ, deriv (deriv q) x * deriv (deriv q) x - (1 / 2 : ℝ) * (q x * deriv (deriv q) x)) +
          (∫ x : ℝ, (1 / 16 : ℝ) * (q x * q x)) :=
        integral_add (hi2.sub (hi02.const_mul (1 / 2 : ℝ))) (hi0.const_mul (1 / 16 : ℝ))
      _ = _ := by
        rw [integral_sub hi2 (hi02.const_mul (1 / 2 : ℝ)), integral_const_mul, integral_const_mul]
  rw [hsplit, hparts]
  simp only [pow_two]
  ring

theorem poleKilled_universalSincSource_norm_sq {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, ‖universalSincKernel s x‖ ^ 2) =
      (s ^ 5)⁻¹ * (∫ x : ℝ, (deriv (deriv (universalSincSource 1)) x) ^ 2) +
        (1 / 2 : ℝ) * (s ^ 3)⁻¹ * (∫ x : ℝ, (deriv (universalSincSource 1) x) ^ 2) +
        (1 / 16 : ℝ) * s⁻¹ * (∫ x : ℝ, (universalSincSource 1 x) ^ 2) := by
  rw [real_source_kernel_energy s hs]
  have h0 := universalSincSource_iteratedDeriv_energy_scale hs 0
  have h1 := universalSincSource_iteratedDeriv_energy_scale hs 1
  have h2 := universalSincSource_iteratedDeriv_energy_scale hs 2
  norm_num only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.mul_zero, Nat.zero_add,
    Nat.reduceAdd, Nat.reduceMul, pow_one] at h0 h1 h2
  rw [h0, h1, h2]
  ring

theorem universalSincSource_gevrey_bound {s : ℝ} (hs : 0 < s) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧ ∀ (r : ℕ) (x : ℝ),
      ‖iteratedDeriv r (universalSincSource s) x‖ ≤ C * H ^ r * (Nat.factorial r : ℝ) ^ 2 := by
  have hb := UniversalSinc.gevreyMomentScale_pos hs
  refine ⟨4 / (Real.pi * UniversalSinc.gevreyMomentScale s ^ 2),
    12 / UniversalSinc.gevreyMomentScale s ^ 2, by positivity, by positivity, ?_⟩
  intro r x
  have he := real_iteratedDeriv_complex (universalSincSource s) (universalSincSource_contDiff hs) r
  have h := UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_gevrey hs r x
  rw [UniversalSinc.inverseCandidate_eq_originalDensityComplex hs] at h
  change ‖iteratedDeriv r (fun y => (universalSincSource s y : ℂ)) x‖ ≤ _ at h
  rw [he, Complex.norm_real] at h
  exact h

theorem universalSincProduct_decay {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ‖UniversalSinc.product s (x : ℂ)‖ ≤
      2 * Real.exp (-(Real.log 2 / 2) * Real.sqrt (s * |x|)) :=
  UniversalSinc.product_norm_ofReal_le_gevrey hs x

end Zeta23.CCM

#print axioms Zeta23.CCM.universalSincProduct_scale
#print axioms Zeta23.CCM.universalSincSource_complex_scale
#print axioms Zeta23.CCM.universalSincSource_scale
#print axioms Zeta23.CCM.universalSincSource_iteratedDeriv_scale
#print axioms Zeta23.CCM.universalSincSource_iteratedDeriv_energy_scale
#print axioms Zeta23.CCM.universalSincKernel_eq_real
#print axioms Zeta23.CCM.poleKilled_universalSincSource_norm_sq
#print axioms Zeta23.CCM.universalSincSource_gevrey_bound
#print axioms Zeta23.CCM.universalSincProduct_decay
