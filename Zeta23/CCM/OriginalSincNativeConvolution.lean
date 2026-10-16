import Zeta23.CCM.NativeCompactTranslateCalculus
import Zeta23.CCM.UniversalSincPhysicalBounds

/-!
# Local convolution identities for the literal original source

Each convolution exchange uses one finite arithmetic cutoff on the
compact integration interval. No global square integrability of X is used.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped Topology

namespace Zeta23.CCM

theorem nativeComplexConvolution_supported {s r : ℝ} {q j : ℝ → ℂ}
    (hq : NativeComplexSourceSupported s q) (hj : NativeComplexSourceSupported r j) :
    NativeComplexSourceSupported (s + r) (fun u => ∫ x : ℝ, q x * j (u - x)) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra hout
  apply hu
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc (-s) s
  · have hjout : u - x ∉ Icc (-r) r := by
      intro hy
      apply hout
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    rw [image_eq_zero_of_notMem_tsupport (fun h => hjout (hj h)), mul_zero]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hq h)), zero_mul]
    rfl

theorem nativeComplexPrimeField_convolution {s r : ℝ} {q j : ℝ → ℂ}
    (hq : NativeComplexSourceSupported s q) (hj : NativeComplexSourceSupported r j)
    (hqc : Continuous q) (hjc : Continuous j) (t : ℝ) :
    nativeComplexPrimeField (fun u => ∫ x : ℝ, q x * j (u - x)) t =
      ∫ x : ℝ, q x * nativeComplexPrimeField j (t - x) := by
  let M := nativeHistoryCutoff (s + r) t + 1
  have hi (n : ℕ) : Integrable (fun x : ℝ =>
      (nativePrimeCoefficient n : ℂ) * (q x * j (t - Real.log n - x))) :=
    ((hqc.mul (hjc.comp (by fun_prop))).integrable_of_hasCompactSupport
      hq.hasCompactSupport.mul_right).const_mul _
  rw [nativeComplexPrimeField_eq_history_sum (nativeComplexConvolution_supported hq hj) le_rfl]
  calc
    (∑ n ∈ range M, (nativePrimeCoefficient n : ℂ) *
        ∫ x : ℝ, q x * j (t - Real.log n - x)) =
        ∫ x : ℝ, ∑ n ∈ range M, (nativePrimeCoefficient n : ℂ) *
          (q x * j (t - Real.log n - x)) := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ (fun n _ => hi n)).symm
    _ = ∫ x : ℝ, q x * nativeComplexPrimeField j (t - x) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Icc (-s) s
      · have ht : t - x ≤ t + s := by linarith [hx.1]
        rw [nativeComplexPrimeField_eq_history_sum hj ht]
        have hM : nativeHistoryCutoff r (t + s) + 1 = M := by
          simp only [M, nativeHistoryCutoff, add_assoc]
        rw [hM, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have he : t - Real.log n - x = t - x - Real.log n := by ring
        rw [he]
        ring
      · have hqx : q x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hq h))
        simp only [hqx, zero_mul, mul_zero, Finset.sum_const_zero]

private theorem real_deriv_cast (g : ℝ → ℝ) (hg : Differentiable ℝ g) :
    deriv (fun x => (g x : ℂ)) = fun x => ((deriv g x : ℝ) : ℂ) := by
  funext x
  exact ((hg x).hasDerivAt.ofReal_comp).deriv

theorem universalSincSecondKernel_eq_real {s : ℝ} (hs : 0 < s) (x : ℝ) :
    universalSincSecondKernel s x = (universalSincSecondSource s x : ℂ) := by
  let g : ℝ → ℝ := fun y => (universalSincKernel s y).re
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    Complex.reCLM.contDiff.comp (universalSincKernel_contDiff hs)
  have hk : universalSincKernel s = fun y => (g y : ℂ) := by
    funext y
    dsimp [g]
    rw [universalSincKernel_eq_real s hs y]
    simp only [Complex.ofReal_re]
  have hdg : Differentiable ℝ (deriv g) :=
    ((contDiff_infty_iff_deriv.mp hg).2).differentiable (by norm_num)
  have he : universalSincSecondKernel s x =
      ((deriv (deriv g) x - (1 / 4 : ℝ) * g x : ℝ) : ℂ) := by
    unfold universalSincSecondKernel universalSincDifferential
    rw [hk, real_deriv_cast g (hg.differentiable (by norm_num)), real_deriv_cast (deriv g) hdg]
    push_cast
    rfl
  change universalSincSecondKernel s x = ((universalSincSecondKernel s x).re : ℂ)
  rw [he]
  simp only [Complex.ofReal_re]

def nativeOriginalKernelPrimeField : ℝ → ℂ :=
  nativeComplexPrimeField (universalSincKernel UniversalSinc.fixedScale)

theorem nativeOriginalKernelPrimeField_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) nativeOriginalKernelPrimeField :=
  nativeComplexPrimeField_contDiff (universalSincKernel_support UniversalSinc.fixedScale_pos)
    (universalSincKernel_contDiff UniversalSinc.fixedScale_pos)

theorem nativeOriginalKernelPrimeField_poleImage :
    universalSincDifferential nativeOriginalKernelPrimeField =
      fun t => (nativeOriginalPrimeField t : ℂ) := by
  rw [nativeOriginalKernelPrimeField, nativeComplexPrimeField_poleImage
    (universalSincKernel_support UniversalSinc.fixedScale_pos)
    ((universalSincKernel_contDiff UniversalSinc.fixedScale_pos).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  have hj : universalSincDifferential (universalSincKernel UniversalSinc.fixedScale) =
      fun t => (nativeOriginalSource t : ℂ) := by
    funext t
    exact universalSincSecondKernel_eq_real UniversalSinc.fixedScale_pos t
  rw [hj]
  funext t
  exact nativeComplexPrimeField_ofReal nativeOriginalSource_supported t

theorem originalDetector_correlationField_eq_sourceConvolution (t : ℝ) :
    nativeComplexPrimeField (fun u => ∫ x : ℝ,
        universalSincKernel UniversalSinc.fixedScale x *
          universalSincKernel UniversalSinc.fixedScale (u - x)) t =
      ∫ x : ℝ, UniversalSinc.originalDensityComplex UniversalSinc.fixedScale x *
        (nativeOriginalPrimeField (t - x) : ℂ) := by
  have hconv : (fun u => ∫ x : ℝ,
      universalSincKernel UniversalSinc.fixedScale x *
        universalSincKernel UniversalSinc.fixedScale (u - x)) =
      fun u => ∫ x : ℝ, UniversalSinc.originalDensityComplex UniversalSinc.fixedScale x *
        (nativeOriginalSource (u - x) : ℂ) := by
    funext u
    rw [universalSincKernel_selfConvolution_eq_source_second UniversalSinc.fixedScale_pos u]
    apply integral_congr_ae
    filter_upwards with x
    rw [universalSincSecondKernel_eq_real UniversalSinc.fixedScale_pos]
    rfl
  rw [hconv]
  change nativeComplexPrimeField (fun u => ∫ x : ℝ,
    (universalSincSource UniversalSinc.fixedScale x : ℂ) *
      (nativeOriginalSource (u - x) : ℂ)) t = _
  rw [nativeComplexPrimeField_convolution
    (NativeComplexSourceSupported.ofReal (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (universalSincSource_support
        UniversalSinc.fixedScale_pos h))))
    (NativeComplexSourceSupported.ofReal nativeOriginalSource_supported)
    (Complex.continuous_ofReal.comp (universalSincSource_contDiff UniversalSinc.fixedScale_pos).continuous)
    (Complex.continuous_ofReal.comp nativeOriginalSource_contDiff.continuous)]
  apply integral_congr_ae
  filter_upwards with x
  rw [nativeComplexPrimeField_ofReal nativeOriginalSource_supported]
  rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeComplexConvolution_supported
#print axioms Zeta23.CCM.nativeComplexPrimeField_convolution
#print axioms Zeta23.CCM.universalSincSecondKernel_eq_real
#print axioms Zeta23.CCM.nativeOriginalKernelPrimeField_contDiff
#print axioms Zeta23.CCM.nativeOriginalKernelPrimeField_poleImage
#print axioms Zeta23.CCM.originalDetector_correlationField_eq_sourceConvolution
