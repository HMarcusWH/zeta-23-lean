import Zeta23.CCM.UniversalSincSourceCharacteristic

/-!
# Exact prefix/tail convolution splitting of the original source law

The tail remains the literal original weighted coordinate sum after the
chosen prefix. Its probability law and product transform are constructed,
then finite-measure characteristic uniqueness proves the exact convolution
split. This is the source-law step needed before convolving an actual
continuous prefix density with its actual tail probability measure.
-/

noncomputable section

open Filter Finset Set MeasureTheory ProbabilityTheory Complex
open scoped Topology BigOperators

namespace Zeta23.CCM.UniversalSinc

def sourceSampleTail (s : ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℝ :=
  sourceSampleSum s ω - sourceSamplePartialSum s N ω

def originalSourceTailLaw (s : ℝ) (N : ℕ) : Measure ℝ :=
  sourceCoordinateLaw.map (sourceSampleTail s N)

def sourceSampleTailPartial (s : ℝ) (N M : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range M, width s (n + N) * unitClamp (ω (n + N))

theorem measurable_sourceSampleTail {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    Measurable (sourceSampleTail s N) :=
  (measurable_sourceSampleSum hs).sub (measurable_sourceSamplePartialSum s N)

theorem originalSourceTailLaw_isProbabilityMeasure {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    IsProbabilityMeasure (originalSourceTailLaw s N) :=
  Measure.isProbabilityMeasure_map (measurable_sourceSampleTail hs N).aemeasurable

theorem sourceSampleTail_abs_le {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (ω : ℕ → ℝ) :
    |sourceSampleTail s N ω| ≤ s / ((N : ℝ) + 1) :=
  sourceSampleSum_sub_partial_abs_le hs N ω

theorem sourceSampleTail_eq_tsum {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (ω : ℕ → ℝ) :
    sourceSampleTail s N ω =
      ∑' n : ℕ, width s (n + N) * unitClamp (ω (n + N)) := by
  have hsplit := (sourceSample_summable hs ω).sum_add_tsum_nat_add N
  unfold sourceSampleTail sourceSampleSum sourceSamplePartialSum
  linarith [hsplit]

theorem measurable_sourceSampleTailPartial (s : ℝ) (N M : ℕ) :
    Measurable (sourceSampleTailPartial s N M) := by
  unfold sourceSampleTailPartial
  exact (range M).measurable_fun_sum fun n _ => measurable_const.mul
    (continuous_unitClamp.measurable.comp (measurable_pi_apply (n + N)))

theorem tendsto_sourceSampleTailPartial {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (ω : ℕ → ℝ) :
    Tendsto (fun M : ℕ => sourceSampleTailPartial s N M ω) atTop
      (𝓝 (sourceSampleTail s N ω)) := by
  rw [sourceSampleTail_eq_tsum hs N ω]
  exact ((summable_nat_add_iff N).mpr (sourceSample_summable hs ω)).hasSum.tendsto_sum_nat

theorem charFun_sourceSampleTailPartial (s x : ℝ) (N M : ℕ) :
    charFun (sourceCoordinateLaw.map (sourceSampleTailPartial s N M)) x =
      ∏ n ∈ range M, sinc ((width s (n + N) : ℂ) * (x : ℂ)) := by
  have hind : iIndepFun
      (fun n (ω : ℕ → ℝ) => width s n * unitClamp (ω n)) sourceCoordinateLaw := by
    exact iIndepFun_infinitePi
      (fun n => measurable_const.mul continuous_unitClamp.measurable)
  have hoff := hind.precomp (fun i j h => Nat.add_right_cancel h :
    Function.Injective (fun n : ℕ => n + N))
  have hfactor := (hoff.restrict (range M)).charFun_map_fun_finsetSum_eq_prod
    (fun n _ => (measurable_const.mul
      (continuous_unitClamp.measurable.comp (measurable_pi_apply (n + N)))).aemeasurable)
  have hpoint := congrFun hfactor x
  change charFun (sourceCoordinateLaw.map (sourceSampleTailPartial s N M)) x =
    ∏ n ∈ range M, charFun (sourceCoordinateLaw.map
      (fun ω : ℕ → ℝ => width s (n + N) * unitClamp (ω (n + N)))) x at hpoint
  rw [hpoint]
  apply Finset.prod_congr rfl
  intro n _
  rw [sourceSampleAtom_map_eq_scaled_box, charFun_map_mul, charFun_centeredUnitBoxLaw,
    Complex.ofReal_mul]

private theorem tail_complex_norm_instances_eq :
    Complex.instNormedAddCommGroup.toNorm = Complex.instNorm := by rfl

/-- The actual tail-law characteristic function is the actual product tail. -/
theorem charFun_originalSourceTailLaw {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (x : ℝ) :
    charFun (originalSourceTailLaw s N) x =
      ∏' n : ℕ, sinc ((width s (n + N) : ℂ) * (x : ℂ)) := by
  have hpartial M : charFun (sourceCoordinateLaw.map (sourceSampleTailPartial s N M)) x =
      ∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSampleTailPartial s N M ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw := by
    rw [charFun_apply_real, integral_map
      (measurable_sourceSampleTailPartial s N M).aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  have htail : charFun (originalSourceTailLaw s N) x =
      ∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSampleTail s N ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw := by
    unfold originalSourceTailLaw
    rw [charFun_apply_real, integral_map
      (measurable_sourceSampleTail hs N).aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  have hlim : Tendsto (fun M : ℕ =>
      ∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSampleTailPartial s N M ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw) atTop
      (𝓝 (∫ ω : ℕ → ℝ, Complex.exp (((x * sourceSampleTail s N ω : ℝ) : ℂ) * I)
        ∂sourceCoordinateLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℕ → ℝ => (1 : ℝ))
    · intro M
      exact (Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp
          (measurable_const.mul (measurable_sourceSampleTailPartial s N M))).mul
          measurable_const)).aestronglyMeasurable
    · exact integrable_const 1
    · intro M
      filter_upwards with ω
      have hb := (Complex.norm_exp_ofReal_mul_I (x * sourceSampleTailPartial s N M ω)).le
      rw [← tail_complex_norm_instances_eq] at hb
      exact hb
    · filter_upwards with ω
      exact Complex.continuous_exp.continuousAt.tendsto.comp
        (((tendsto_sourceSampleTailPartial hs N ω).const_mul x).ofReal.mul_const I)
  have hcharlim : Tendsto (fun M : ℕ =>
      ∏ n ∈ range M, sinc ((width s (n + N) : ℂ) * (x : ℂ))) atTop
      (𝓝 (charFun (originalSourceTailLaw s N) x)) := by
    simpa only [← hpartial, charFun_sourceSampleTailPartial, ← htail] using hlim
  have hprod := ((multipliable_nat_add_iff N).mpr
    (multipliable_sinc hs (x : ℂ))).hasProd.tendsto_prod_nat
  exact tendsto_nhds_unique hcharlim hprod

/-- Exact convolution splitting is proved by the actual law transforms,
without accepting a prefix/tail independence or density bridge as input. -/
theorem originalSourceLaw_eq_prefix_conv_tail {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    originalSourceLaw s =
      (sourceCoordinateLaw.map (sourceSamplePartialSum s N)) ∗ originalSourceTailLaw s N := by
  letI : IsProbabilityMeasure (originalSourceLaw s) := originalSourceLaw_isProbabilityMeasure hs
  letI : IsProbabilityMeasure (sourceCoordinateLaw.map (sourceSamplePartialSum s N)) :=
    Measure.isProbabilityMeasure_map (measurable_sourceSamplePartialSum s N).aemeasurable
  letI : IsProbabilityMeasure (originalSourceTailLaw s N) := originalSourceTailLaw_isProbabilityMeasure hs N
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_conv, charFun_originalSourceLaw hs, charFun_sourceSamplePartialSum,
    charFun_originalSourceTailLaw hs]
  exact ((multipliable_sinc hs (x : ℂ)).prod_mul_tprod_nat_add N).symm

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.sourceSampleTail_abs_le
#print axioms Zeta23.CCM.UniversalSinc.charFun_originalSourceTailLaw
#print axioms Zeta23.CCM.UniversalSinc.originalSourceLaw_eq_prefix_conv_tail
