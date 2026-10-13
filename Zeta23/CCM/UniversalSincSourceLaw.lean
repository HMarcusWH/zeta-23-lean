import Zeta23.CCM.UniversalSincDetector
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The actual compact probability law of the prescribed infinite source

Independent coordinates are uniform on the unit centered interval; the
original widths scale them before summation. Clamping makes the sample sum
converge at every point of the sample space and does not change it almost
surely. This constructs an actual compactly supported probability law.
Its characteristic function and its identification with a smooth inverse
Fourier density are separate obligations, not premises of this construction.
-/

noncomputable section

open Filter Finset Set MeasureTheory
open scoped Topology BigOperators

namespace Zeta23.CCM.UniversalSinc

/-- Normalized Lebesgue measure on the centered unit interval. -/
def centeredUnitBoxLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (-1 : ℝ) 1)

instance centeredUnitBoxLaw_isProbabilityMeasure : IsProbabilityMeasure centeredUnitBoxLaw := by
  unfold centeredUnitBoxLaw
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    norm_num
  · rw [Real.volume_Icc]
    simp

theorem centeredUnitBoxLaw_interval_mass : centeredUnitBoxLaw (Icc (-1 : ℝ) 1) = 1 := by
  unfold centeredUnitBoxLaw
  apply ProbabilityTheory.cond_apply_self
  · rw [Real.volume_Icc]
    norm_num
  · rw [Real.volume_Icc]
    simp

theorem centeredUnitBoxLaw_ae_mem : ∀ᵐ x ∂centeredUnitBoxLaw, x ∈ Icc (-1 : ℝ) 1 := by
  exact (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr centeredUnitBoxLaw_interval_mass

/-- The explicit common-coordinate product probability space. -/
def sourceCoordinateLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => centeredUnitBoxLaw)

instance sourceCoordinateLaw_isProbabilityMeasure : IsProbabilityMeasure sourceCoordinateLaw := by
  unfold sourceCoordinateLaw
  infer_instance

/-- This bounded extension is exactly the coordinate on its probability support. -/
def unitClamp (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem unitClamp_abs_le_one (x : ℝ) : |unitClamp x| ≤ 1 := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem unitClamp_eq_self_of_mem {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : unitClamp x = x := by
  rw [unitClamp, min_eq_right hx.2, max_eq_right hx.1]

theorem continuous_unitClamp : Continuous unitClamp :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The actual infinite source sample with the specified telescoping widths. -/
def sourceSampleSum (s : ℝ) (ω : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, width s n * unitClamp (ω n)

def sourceSamplePartialSum (s : ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, width s n * unitClamp (ω n)

theorem sourceSampleAtom_norm_le_width {s : ℝ} (hs : 0 ≤ s) (ω : ℕ → ℝ) (n : ℕ) :
    ‖width s n * unitClamp (ω n)‖ ≤ width s n := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (width_nonneg hs n)]
  exact (mul_le_mul_of_nonneg_left (unitClamp_abs_le_one _) (width_nonneg hs n)).trans_eq
    (mul_one _)

theorem sourceSample_summable {s : ℝ} (hs : 0 ≤ s) (ω : ℕ → ℝ) :
    Summable (fun n : ℕ => width s n * unitClamp (ω n)) :=
  (hasSum_width hs).summable.of_norm_bounded (sourceSampleAtom_norm_le_width hs ω)

theorem sourceSampleSum_abs_le {s : ℝ} (hs : 0 ≤ s) (ω : ℕ → ℝ) :
    |sourceSampleSum s ω| ≤ s := by
  simpa only [sourceSampleSum, Real.norm_eq_abs] using
    tsum_of_norm_bounded (hasSum_width hs) (sourceSampleAtom_norm_le_width hs ω)

/-- The actual source sum has the exact deterministic telescoping tail bound. -/
theorem sourceSampleSum_sub_partial_abs_le {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (ω : ℕ → ℝ) :
    |sourceSampleSum s ω - sourceSamplePartialSum s N ω| ≤ s / ((N : ℝ) + 1) := by
  have hsplit := (sourceSample_summable hs ω).sum_add_tsum_nat_add N
  have heq : sourceSampleSum s ω - sourceSamplePartialSum s N ω =
      ∑' n : ℕ, width s (n + N) * unitClamp (ω (n + N)) := by
    unfold sourceSampleSum sourceSamplePartialSum
    linarith [hsplit]
  rw [heq]
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded (hasSum_tail_width hs N)
    (fun n => sourceSampleAtom_norm_le_width hs ω (n + N))

theorem measurable_sourceSamplePartialSum (s : ℝ) (N : ℕ) :
    Measurable (sourceSamplePartialSum s N) := by
  unfold sourceSamplePartialSum
  exact (range N).measurable_fun_sum fun n _ =>
    measurable_const.mul (continuous_unitClamp.measurable.comp (measurable_pi_apply n))

theorem tendsto_sourceSamplePartialSum {s : ℝ} (hs : 0 ≤ s) (ω : ℕ → ℝ) :
    Tendsto (fun N : ℕ => sourceSamplePartialSum s N ω) atTop (𝓝 (sourceSampleSum s ω)) :=
  (sourceSample_summable hs ω).hasSum.tendsto_sum_nat

theorem measurable_sourceSampleSum {s : ℝ} (hs : 0 ≤ s) : Measurable (sourceSampleSum s) := by
  apply measurable_of_tendsto_metrizable (measurable_sourceSamplePartialSum s)
  exact tendsto_pi_nhds.mpr (tendsto_sourceSamplePartialSum hs)

theorem sourceCoordinateLaw_ae_unit_interval :
    ∀ᵐ ω ∂sourceCoordinateLaw, ∀ n : ℕ, ω n ∈ Icc (-1 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro n
  have hbox := centeredUnitBoxLaw_ae_mem
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => centeredUnitBoxLaw) n] at hbox
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable hbox

/-- Clamping changes no source sample almost surely: the construction is
the prescribed sum of independent uniform variables, not a surrogate. -/
theorem sourceSampleSum_ae_eq_unclamped (s : ℝ) :
    sourceSampleSum s =ᵐ[sourceCoordinateLaw]
      (fun ω : ℕ → ℝ => ∑' n : ℕ, width s n * ω n) := by
  filter_upwards [sourceCoordinateLaw_ae_unit_interval] with ω hω
  unfold sourceSampleSum
  apply tsum_congr
  intro n
  rw [unitClamp_eq_self_of_mem (hω n)]

/-- The native source scales linearly on the same probability space. -/
theorem sourceSampleSum_eq_scale (s : ℝ) (ω : ℕ → ℝ) :
    sourceSampleSum s ω = s * sourceSampleSum 1 ω := by
  unfold sourceSampleSum
  have hterm : ∀ n : ℕ, width s n * unitClamp (ω n) =
      s * (width 1 n * unitClamp (ω n)) := by
    intro n
    unfold width
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]

/-- The actual prescribed infinite-convolution probability law. -/
def originalSourceLaw (s : ℝ) : Measure ℝ :=
  sourceCoordinateLaw.map (sourceSampleSum s)

theorem originalSourceLaw_isProbabilityMeasure {s : ℝ} (hs : 0 ≤ s) :
    IsProbabilityMeasure (originalSourceLaw s) :=
  Measure.isProbabilityMeasure_map (measurable_sourceSampleSum hs).aemeasurable

theorem originalSourceLaw_interval_mass {s : ℝ} (hs : 0 ≤ s) :
    originalSourceLaw s (Icc (-s) s) = 1 := by
  unfold originalSourceLaw
  rw [Measure.map_apply (measurable_sourceSampleSum hs) measurableSet_Icc]
  have hpre : sourceSampleSum s ⁻¹' Icc (-s) s = univ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_univ, iff_true]
    exact abs_le.mp (sourceSampleSum_abs_le hs ω)
  rw [hpre]
  exact measure_univ

/-- Scaling is an equality of the actual probability laws, with no density
or Fourier identification accepted as input. -/
theorem originalSourceLaw_eq_map_scale (s : ℝ) :
    originalSourceLaw s = (originalSourceLaw 1).map (fun x : ℝ => s * x) := by
  unfold originalSourceLaw
  have hscale : Measurable (fun x : ℝ => s * x) := measurable_const.mul measurable_id
  rw [Measure.map_map hscale
    (measurable_sourceSampleSum (by norm_num : (0 : ℝ) ≤ 1))]
  congr 1
  funext ω
  exact sourceSampleSum_eq_scale s ω

theorem fixed_originalSourceLaw_isProbabilityMeasure :
    IsProbabilityMeasure (originalSourceLaw fixedScale) :=
  originalSourceLaw_isProbabilityMeasure fixedScale_pos.le

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.sourceSampleSum_sub_partial_abs_le
#print axioms Zeta23.CCM.UniversalSinc.sourceSampleSum_ae_eq_unclamped
#print axioms Zeta23.CCM.UniversalSinc.originalSourceLaw_isProbabilityMeasure
#print axioms Zeta23.CCM.UniversalSinc.originalSourceLaw_interval_mass
#print axioms Zeta23.CCM.UniversalSinc.originalSourceLaw_eq_map_scale
#print axioms Zeta23.CCM.UniversalSinc.fixed_originalSourceLaw_isProbabilityMeasure
