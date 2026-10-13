import Zeta23.CCM.UniversalSincDetectorBounds
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Actual inverse-Fourier precursor for the original product

The prescribed product has integrable polynomial moments. Its inverse in
the paper convention is therefore an actual smooth function with the
visible normalization `1/(2π)` and negative inverse phase. It is named a
candidate because probability positivity, compact support, total mass and
the identity of its forward transform with the product are separate
construction obligations. None is accepted as a premise or asserted here.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology FourierTransform

namespace Zeta23.CCM.UniversalSinc

/-- The real envelope needed for every polynomial moment is integrable.
The positive-half-line theorem uses power `p=1/2`; reflection supplies the
other half-line without a change of decay constant. -/
theorem integrable_polynomial_sqrt_decay (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| ^ k * Real.exp (-b * Real.sqrt |x|)) := by
  have hi : IntegrableOn
      (fun x : ℝ => |x| ^ k * Real.exp (-b * Real.sqrt |x|)) (Ioi 0) := by
    have hraw := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (k : ℝ)) (p := (1 / 2 : ℝ))
      (by linarith [Nat.cast_nonneg (R := ℝ) k] : (-1 : ℝ) < (k : ℝ))
      (by norm_num) hb
    refine hraw.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hx), Real.sqrt_eq_rpow, Real.rpow_natCast]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hi⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hi

private theorem inverse_complex_norm_instances_eq :
    Complex.instNormedAddCommGroup.toNorm = Complex.instNorm := by
  rfl

theorem continuous_product_ofReal {s : ℝ} (hs : 0 ≤ s) :
    Continuous (fun x : ℝ => product s (x : ℂ)) :=
  (differentiable_product hs).continuous.comp Complex.continuous_ofReal

/-- Every actual Fourier-product polynomial moment is absolutely integrable. -/
theorem integrable_product_ofReal_norm_moment {s : ℝ} (hs : 0 < s) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k * ‖product s (x : ℂ)‖) := by
  let b : ℝ := (Real.log 2 / 2) * Real.sqrt s
  have hb : 0 < b := mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (Real.sqrt_pos.mpr hs)
  have henv := (integrable_polynomial_sqrt_decay k hb).const_mul (2 : ℝ)
  apply henv.mono'
  · have hc := ((continuous_id.abs.pow k).mul (continuous_product_ofReal hs.le).norm)
    rw [inverse_complex_norm_instances_eq] at hc
    exact hc.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg x) k)
      (Complex.norm_nonneg _))]
    have hp := product_norm_ofReal_le_gevrey hs x
    have hphase : -(Real.log 2 / 2) * Real.sqrt (s * |x|) = -b * Real.sqrt |x| := by
      rw [Real.sqrt_mul hs.le]
      dsimp only [b]
      ring
    rw [hphase] at hp
    exact (mul_le_mul_of_nonneg_left hp (pow_nonneg (abs_nonneg x) k)).trans_eq
      (by ring)

/-- The prescribed real-axis product itself is an integrable complex function. -/
theorem integrable_product_ofReal {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => product s (x : ℂ)) := by
  have hn : Integrable (fun x : ℝ => ‖product s (x : ℂ)‖) := by
    simpa only [pow_zero, one_mul] using integrable_product_ofReal_norm_moment hs 0
  rw [← inverse_complex_norm_instances_eq] at hn
  exact (integrable_norm_iff (continuous_product_ofReal hs.le).aestronglyMeasurable).mp hn

/-- The actual inverse integral in the paper convention. The complex-valued
function is not yet claimed to be the infinite-convolution probability density. -/
def inverseCandidate (s : ℝ) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    Zeta23.paperFT (fun ξ : ℝ => product s (ξ : ℂ)) ((-x : ℝ) : ℂ)

theorem inverseCandidate_eq_fourier (s x : ℝ) :
    inverseCandidate s x = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (𝓕 (fun ξ : ℝ => product s (ξ : ℂ))) (x / (2 * Real.pi)) := by
  unfold inverseCandidate
  rw [Zeta23.paperFT_ofReal_eq_fourier]
  simp only [neg_neg]

/-- The inverse precursor is smooth, derived solely from the actual moments. -/
theorem contDiff_inverseCandidate {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (inverseCandidate s) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (fun ξ : ℝ => product s (ξ : ℂ))) := by
    apply Real.contDiff_fourier
    intro n _
    have hm := integrable_product_ofReal_norm_moment hs n
    rw [← inverse_complex_norm_instances_eq] at hm
    simpa only [Real.norm_eq_abs] using hm
  have heq : inverseCandidate s = fun x : ℝ =>
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (𝓕 (fun ξ : ℝ => product s (ξ : ℂ))) (x / (2 * Real.pi)) := by
    funext x
    exact inverseCandidate_eq_fourier s x
  rw [heq]
  exact contDiff_const.mul (hF.comp (contDiff_id.div_const (2 * Real.pi)))

theorem continuous_inverseCandidate {s : ℝ} (hs : 0 < s) :
    Continuous (inverseCandidate s) := (contDiff_inverseCandidate hs).continuous

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.integrable_product_ofReal_norm_moment
#print axioms Zeta23.CCM.UniversalSinc.integrable_product_ofReal
#print axioms Zeta23.CCM.UniversalSinc.inverseCandidate_eq_fourier
#print axioms Zeta23.CCM.UniversalSinc.contDiff_inverseCandidate
