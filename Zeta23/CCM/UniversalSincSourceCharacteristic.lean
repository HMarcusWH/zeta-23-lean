import Zeta23.CCM.UniversalSincSourceLaw
import Zeta23.CCM.UniversalSincDetectorBounds
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The original source law has the actual sinc-product characteristic function

This connects the explicit infinite product with the explicit probability
law. Finite independent sums give finite sinc products. Pathwise source
convergence and the unit norm of the real characteristic kernel justify
dominated convergence, while the proved product-prefix convergence gives
the same limit. No density or physical Fourier identification is assumed.
-/

noncomputable section

open Filter Finset Set MeasureTheory ProbabilityTheory Complex
open scoped Topology BigOperators

namespace Zeta23.CCM.UniversalSinc

private theorem characteristic_complex_norm_instances_eq :
    Complex.instNormedAddCommGroup.toNorm = Complex.instNorm := by
  rfl

/-- Exact normalized Lebesgue-box characteristic function, including the
removable singularity and negative arguments. -/
theorem charFun_centeredUnitBoxLaw (r : ℝ) :
    charFun centeredUnitBoxLaw r = sinc (r : ℂ) := by
  by_cases hr : r = 0
  · simp [hr]
  rw [charFun_apply_real]
  unfold centeredUnitBoxLaw ProbabilityTheory.cond
  rw [integral_smul_measure]
  have hvol : (volume (Icc (-1 : ℝ) 1))⁻¹.toReal = (1 / 2 : ℝ) := by
    rw [Real.volume_Icc]
    norm_num
  rw [hvol, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hi : (∫ x in (-1 : ℝ)..1, Complex.exp ((r : ℂ) * (x : ℂ) * I)) =
      ((2 : ℝ) : ℂ) * (Real.sinc r : ℂ) := by
    have hchange := intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => Complex.exp ((x : ℂ) * I)) (a := (-1 : ℝ)) (b := 1) hr
    simp only [Complex.ofReal_mul, mul_neg, mul_one, neg_mul, one_mul] at hchange
    rw [hchange, integral_exp_mul_I_eq_sinc]
    rw [Complex.real_smul]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero, add_zero,
        zero_add] <;>
      field_simp [hr] <;> ring
  rw [hi, RCLike.real_smul_eq_coe_mul, sinc_ofReal]
  push_cast <;> ring

theorem sourceSampleAtom_map_eq_scaled_box (s : ℝ) (n : ℕ) :
    sourceCoordinateLaw.map (fun ω : ℕ → ℝ => width s n * unitClamp (ω n)) =
      centeredUnitBoxLaw.map (fun x : ℝ => width s n * x) := by
  have hcomp : (fun ω : ℕ → ℝ => width s n * unitClamp (ω n)) =
      (fun x : ℝ => width s n * unitClamp x) ∘ (fun ω : ℕ → ℝ => ω n) := rfl
  have hm : Measurable (fun x : ℝ => width s n * unitClamp x) :=
    measurable_const.mul continuous_unitClamp.measurable
  rw [hcomp, ← Measure.map_map hm (measurable_pi_apply n)]
  change ((Measure.infinitePi (fun _ : ℕ => centeredUnitBoxLaw)).map
    (fun ω : ℕ → ℝ => ω n)).map (fun x : ℝ => width s n * unitClamp x) = _
  rw [Measure.infinitePi_map_eval]
  apply Measure.map_congr
  filter_upwards [centeredUnitBoxLaw_ae_mem] with x hx
  rw [unitClamp_eq_self_of_mem hx]

/-- Each original finite sample history has the exact product transform. -/
theorem charFun_sourceSamplePartialSum (s x : ℝ) (N : ℕ) :
    charFun (sourceCoordinateLaw.map (sourceSamplePartialSum s N)) x =
      partialProduct s x N := by
  have hind : iIndepFun
      (fun n (ω : ℕ → ℝ) => width s n * unitClamp (ω n)) sourceCoordinateLaw := by
    exact iIndepFun_infinitePi
      (fun n => measurable_const.mul continuous_unitClamp.measurable)
  have hfactor := (hind.restrict (range N)).charFun_map_fun_finsetSum_eq_prod
    (fun n _ => (measurable_const.mul
      (continuous_unitClamp.measurable.comp (measurable_pi_apply n))).aemeasurable)
  have hpoint := congrFun hfactor x
  simp only [Finset.prod_apply, Function.comp_def, Pi.mul_apply] at hpoint
  change charFun (sourceCoordinateLaw.map (sourceSamplePartialSum s N)) x =
    ∏ n ∈ range N, charFun (sourceCoordinateLaw.map
      (fun ω : ℕ → ℝ => width s n * unitClamp (ω n))) x at hpoint
  rw [hpoint]
  unfold partialProduct
  apply Finset.prod_congr rfl
  intro n _
  rw [sourceSampleAtom_map_eq_scaled_box, charFun_map_mul, charFun_centeredUnitBoxLaw,
    Complex.ofReal_mul]

private theorem charFun_sourceSamplePartialSum_integral (s x : ℝ) (N : ℕ) :
    charFun (sourceCoordinateLaw.map (sourceSamplePartialSum s N)) x =
      ∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSamplePartialSum s N ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw := by
  rw [charFun_apply_real, integral_map
    (measurable_sourceSamplePartialSum s N).aemeasurable (by fun_prop)]
  simp only [Complex.ofReal_mul]

private theorem charFun_originalSourceLaw_integral {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    charFun (originalSourceLaw s) x =
      ∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSampleSum s ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw := by
  unfold originalSourceLaw
  rw [charFun_apply_real, integral_map
    (measurable_sourceSampleSum hs).aemeasurable (by fun_prop)]
  simp only [Complex.ofReal_mul]

/-- The source law's transform is derived by independent finite histories
and dominated convergence, not supplied through a visibility premise. -/
theorem charFun_originalSourceLaw {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    charFun (originalSourceLaw s) x = product s (x : ℂ) := by
  have hlim : Tendsto (fun N : ℕ =>
      ∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSamplePartialSum s N ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw) atTop
      (𝓝 (∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSampleSum s ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℕ → ℝ => (1 : ℝ))
    · intro N
      exact (Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp
          (measurable_const.mul (measurable_sourceSamplePartialSum s N))).mul
          measurable_const)).aestronglyMeasurable
    · exact integrable_const 1
    · intro N
      filter_upwards with ω
      have hb := (Complex.norm_exp_ofReal_mul_I (x * sourceSamplePartialSum s N ω)).le
      rw [← characteristic_complex_norm_instances_eq] at hb
      exact hb
    · filter_upwards with ω
      exact Complex.continuous_exp.continuousAt.tendsto.comp
        (((tendsto_sourceSamplePartialSum hs ω).const_mul x).ofReal.mul_const I)
  have hcharlim : Tendsto (fun N : ℕ => partialProduct s x N) atTop
      (𝓝 (charFun (originalSourceLaw s) x)) := by
    simpa only [← charFun_sourceSamplePartialSum_integral,
      charFun_sourceSamplePartialSum, ← charFun_originalSourceLaw_integral hs] using hlim
  exact tendsto_nhds_unique hcharlim (tendsto_partial_product hs (x : ℂ))

theorem fixed_charFun_originalSourceLaw (x : ℝ) :
    charFun (originalSourceLaw fixedScale) x = product fixedScale (x : ℂ) :=
  charFun_originalSourceLaw fixedScale_pos.le x

/-- The original probability law is exactly reflection invariant, derived
from its actual even characteristic product and measure uniqueness. -/
theorem originalSourceLaw_map_neg {s : ℝ} (hs : 0 ≤ s) :
    (originalSourceLaw s).map (fun x : ℝ => -x) = originalSourceLaw s := by
  letI : IsProbabilityMeasure (originalSourceLaw s) := originalSourceLaw_isProbabilityMeasure hs
  letI : IsProbabilityMeasure ((originalSourceLaw s).map (fun x : ℝ => -x)) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  apply Measure.ext_of_charFun
  funext x
  have hneg : (fun x : ℝ => -x) = (fun x : ℝ => (-1 : ℝ) * x) := by
    funext x
    ring
  rw [hneg, charFun_map_mul, charFun_originalSourceLaw hs, charFun_originalSourceLaw hs]
  simp only [neg_one_mul, Complex.ofReal_neg, product_neg]

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.charFun_centeredUnitBoxLaw
#print axioms Zeta23.CCM.UniversalSinc.charFun_sourceSamplePartialSum
#print axioms Zeta23.CCM.UniversalSinc.charFun_originalSourceLaw
#print axioms Zeta23.CCM.UniversalSinc.fixed_charFun_originalSourceLaw
#print axioms Zeta23.CCM.UniversalSinc.originalSourceLaw_map_neg
