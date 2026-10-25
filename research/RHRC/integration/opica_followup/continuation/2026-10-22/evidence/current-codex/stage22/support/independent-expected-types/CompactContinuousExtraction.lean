import Zeta23.OPICAFollowup.NearGapLimits
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

noncomputable section
open Set Filter MeasureTheory Complex Metric
open scoped Topology ENNReal FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.IndependentCompactExtraction
open Zeta23.OPICA

/- Uniform smooth approximation with one support interval chosen before
epsilon. This is the local-variation control needed to pass from Schwartz
convergence to genuine compactly supported continuous-test convergence. -/
theorem compact_continuous_schwartz_approximation
    (f : ℝ → ℂ) (continuous : Continuous f) (compact : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ tsupport f ⊆ Icc (-R) R ∧
      ∀ ε : ℝ, 0 < ε → ∃ g : SchwartzMap ℝ ℂ,
        tsupport (g : ℝ → ℂ) ⊆ Icc (-R) R ∧ ∀ x, ‖g x - f x‖ ≤ ε := by
  obtain ⟨r, hr, supportBound⟩ := compact.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : ℝ) := ⟨r, r+1, hr, by linarith⟩
  have supportF : tsupport f ⊆ Icc (-(r+1)) (r+1) := by
    intro x hx
    have := supportBound x hx
    rw [Real.norm_eq_abs, abs_le] at this
    constructor <;> linarith [this.1, this.2]
  refine ⟨r+1, by linarith, supportF, fun ε hε => ?_⟩
  have uniformly : UniformContinuous f :=
    continuous.uniformContinuous_of_tendsto_cocompact compact.is_zero_at_infty
  obtain ⟨h, smooth, close⟩ := uniformly.exists_contDiff_dist_le hε
  let g : ℝ → ℂ := fun x => χ x • h x
  have compactG : HasCompactSupport g := χ.hasCompactSupport.smul_right
  have smoothG : ContDiff ℝ (⊤ : ℕ∞) g := χ.contDiff.smul smooth
  refine ⟨compactG.toSchwartzMap smoothG, ?_, ?_⟩
  · intro x hx
    have hxχ : x ∈ tsupport χ := (tsupport_smul_subset_left (χ : ℝ → ℝ) h) hx
    rw [χ.tsupport_eq, mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at hxχ
    exact hxχ
  · intro x
    have cutoff : χ x • f x = f x := by
      by_cases hx : x ∈ tsupport f
      · have heq : χ x = 1 := χ.one_of_mem_closedBall (by
          rw [mem_closedBall, dist_zero_right]
          exact supportBound x hx)
        rw [heq, one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
    change ‖χ x • h x - f x‖ ≤ ε
    rw [← cutoff, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    calc
      χ x * ‖h x - f x‖ ≤ 1 * ‖h x - f x‖ :=
        mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)
      _ ≤ ε := by simpa only [one_mul, ← dist_eq_norm] using (close x).le

def signedCompactPairing (ν : LocallyFiniteSignedMeasure) (f : ℝ → ℂ) : ℂ :=
  (∫ x, f x ∂ν.positive) - (∫ x, f x ∂ν.negative)

theorem compact_pairing_difference_bound
    (ν : LocallyFiniteSignedMeasure) (C R δ : ℝ)
    (common : CommonLinearMassBound C ν.totalVariation) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (f g : ℝ → ℂ) (continuousF : Continuous f) (continuousG : Continuous g)
    (supportF : tsupport f ⊆ Icc (-R) R) (supportG : tsupport g ⊆ Icc (-R) R)
    (close : ∀ x, ‖f x - g x‖ ≤ δ) :
    ‖signedCompactPairing ν f - signedCompactPairing ν g‖ ≤ δ * (C*(1+R)) := by
  have compactF : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) supportF
  have compactG : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) supportG
  have hfp := continuousF.integrable_of_hasCompactSupport compactF (μ := ν.positive)
  have hfn := continuousF.integrable_of_hasCompactSupport compactF (μ := ν.negative)
  have hgp := continuousG.integrable_of_hasCompactSupport compactG (μ := ν.positive)
  have hgn := continuousG.integrable_of_hasCompactSupport compactG (μ := ν.negative)
  have vanish : ∀ x, x ∉ Icc (-R) R → (f x - g x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hf => hx (supportF hf)),
      image_eq_zero_of_notMem_tsupport (fun hg => hx (supportG hg)), sub_self]
  have positiveBound : ‖∫ x, (f x-g x) ∂ν.positive‖ ≤ δ * ν.positive.real (Icc (-R) R) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero vanish]
    exact norm_setIntegral_le_of_norm_le_const_ae' isCompact_Icc.measure_lt_top
      (Eventually.of_forall (fun x _ => close x))
  have negativeBound : ‖∫ x, (f x-g x) ∂ν.negative‖ ≤ δ * ν.negative.real (Icc (-R) R) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero vanish]
    exact norm_setIntegral_le_of_norm_le_const_ae' isCompact_Icc.measure_lt_top
      (Eventually.of_forall (fun x _ => close x))
  have difference : signedCompactPairing ν f - signedCompactPairing ν g =
      (∫ x, (f x-g x) ∂ν.positive) - (∫ x, (f x-g x) ∂ν.negative) := by
    rw [integral_sub hfp hgp, integral_sub hfn hgn]
    simp only [signedCompactPairing]
    ring
  calc
    ‖signedCompactPairing ν f - signedCompactPairing ν g‖ ≤
      ‖∫ x, (f x-g x) ∂ν.positive‖ + ‖∫ x, (f x-g x) ∂ν.negative‖ := by
        rw [difference]; exact norm_sub_le _ _
    _ ≤ δ * ν.positive.real (Icc (-R) R) + δ * ν.negative.real (Icc (-R) R) :=
      add_le_add positiveBound negativeBound
    _ = δ * ν.totalVariation.real (Icc (-R) R) := by
      rw [LocallyFiniteSignedMeasure.totalVariation, measureReal_add_apply
        isCompact_Icc.measure_lt_top.ne isCompact_Icc.measure_lt_top.ne]
      ring
    _ ≤ δ * (C*(1+R)) := mul_le_mul_of_nonneg_left (common.2 R hR) hδ

theorem schwartz_zero_implies_compact_continuous_zero
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, CommonLinearMassBound C (ν n).totalVariation)
    (growth : ∀ n, (ν n).HasLinearGrowth)
    (schwartz : ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (ν n).distributionOfLinearGrowth (growth n) φ) atTop (𝓝 0))
    (f : ℝ → ℂ) (continuous : Continuous f) (compact : HasCompactSupport f) :
    Tendsto (fun n => signedCompactPairing (ν n) f) atTop (𝓝 0) := by
  obtain ⟨R, hR, supportF, approx⟩ := compact_continuous_schwartz_approximation f continuous compact
  have hC : 0 ≤ C := (common 0).1
  let B : ℝ := C*(1+R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε/(2*(B+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have cost : δ*B ≤ ε/2 := by
    have hmul : δ*(2*(B+1)) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨g, supportG, close⟩ := approx δ hδ
  have schwartzG : Tendsto (fun n => signedCompactPairing (ν n) g) atTop (𝓝 0) := by
    simpa only [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply, signedCompactPairing]
      using schwartz g
  obtain ⟨N, bound⟩ := Metric.tendsto_atTop.mp schwartzG (ε/2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have error := compact_pairing_difference_bound (ν n) C R δ (common n) hR.le hδ.le
    f g continuous g.continuous supportF supportG
    (fun x => by simpa only [norm_sub_rev] using close x)
  have small : ‖signedCompactPairing (ν n) g‖ < ε/2 := by
    simpa only [dist_zero_right] using bound n hn
  rw [dist_zero_right]
  calc
    ‖signedCompactPairing (ν n) f‖ =
      ‖(signedCompactPairing (ν n) f - signedCompactPairing (ν n) g) +
        signedCompactPairing (ν n) g‖ := by congr 1; abel
    _ ≤ ‖signedCompactPairing (ν n) f - signedCompactPairing (ν n) g‖ +
      ‖signedCompactPairing (ν n) g‖ := norm_add_le _ _
    _ < ε := by dsimp [B] at cost; linarith

def extractedZeroMeasure : LocallyFiniteSignedMeasure :=
  ⟨0, 0, inferInstance, inferInstance, Measure.MutuallySingular.zero_left⟩

theorem extractedZeroMeasure_growth : extractedZeroMeasure.HasLinearGrowth := by
  refine ⟨0, le_rfl, fun R hR => ?_⟩
  simp [LocallyFiniteSignedMeasure.totalVariation, extractedZeroMeasure]

/- The HT2 conclusion on the genuine C_c topology, not just compact smooth
tests. Every integral is against the actual original Jordan measure. -/
theorem expected_near_gap_compact_continuous_limit_zero
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C*(1+R))
    (growth : ∀ n, (ν n).HasLinearGrowth)
    (selfdual : ∀ n, (ν n).FourierSelfdual (growth n))
    (positiveOff : ∀ n, (ν n).negative integerLatticeᶜ = 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n ∧ a n ≤ 1)
    (gap : ∀ n, (ν n).positive (Ioo (-a n) (a n)) = 0 ∧
      (ν n).negative (Ioo (-a n) (a n)) = 0)
    (sharp : Tendsto a atTop (𝓝 1)) :
    ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => (∫ x, f x ∂(ν n).positive) - (∫ x, f x ∂(ν n).negative))
        atTop (𝓝 ((∫ x, f x ∂extractedZeroMeasure.positive) -
          (∫ x, f x ∂extractedZeroMeasure.negative))) := by
  intro f continuous compact
  have schwartz : ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (ν n).distributionOfLinearGrowth (growth n) φ) atTop (𝓝 0) :=
    near_gap_controlled_limit_zero ν C common selfdual a
      (fun n => (ha n).1) (fun n => (ha n).2) gap positiveOff sharp
  simpa only [signedCompactPairing, extractedZeroMeasure, integral_zero_measure, sub_self] using
    schwartz_zero_implies_compact_continuous_zero ν C common growth schwartz f continuous compact

/- A genuine zero signed-measure limit along a strictly increasing
subsequence. The entire original sequence already converges in C_c tests,
so identity extraction is valid. This is not general Radon compactness. -/
theorem expected_near_gap_genuine_zero_measure_extraction
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C*(1+R))
    (growth : ∀ n, (ν n).HasLinearGrowth)
    (selfdual : ∀ n, (ν n).FourierSelfdual (growth n))
    (positiveOff : ∀ n, (ν n).negative integerLatticeᶜ = 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n ∧ a n ≤ 1)
    (gap : ∀ n, (ν n).positive (Ioo (-a n) (a n)) = 0 ∧
      (ν n).negative (Ioo (-a n) (a n)) = 0)
    (sharp : Tendsto a atTop (𝓝 1)) :
    ∃ subseq : ℕ → ℕ, ∃ limit : LocallyFiniteSignedMeasure,
      StrictMono subseq ∧ limit.positive = 0 ∧ limit.negative = 0 ∧ limit.HasLinearGrowth ∧
      ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
        Tendsto (fun n => (∫ x, f x ∂(ν (subseq n)).positive) -
          (∫ x, f x ∂(ν (subseq n)).negative)) atTop
          (𝓝 ((∫ x, f x ∂limit.positive) - (∫ x, f x ∂limit.negative))) := by
  refine ⟨id, extractedZeroMeasure, strictMono_id, rfl, rfl, extractedZeroMeasure_growth, ?_⟩
  exact expected_near_gap_compact_continuous_limit_zero ν C common growth selfdual positiveOff a ha gap sharp

#print axioms Zeta23.OPICAFollowup.IndependentCompactExtraction.compact_continuous_schwartz_approximation
#print axioms Zeta23.OPICAFollowup.IndependentCompactExtraction.compact_pairing_difference_bound
#print axioms Zeta23.OPICAFollowup.IndependentCompactExtraction.schwartz_zero_implies_compact_continuous_zero
#print axioms Zeta23.OPICAFollowup.IndependentCompactExtraction.expected_near_gap_compact_continuous_limit_zero
#print axioms Zeta23.OPICAFollowup.IndependentCompactExtraction.expected_near_gap_genuine_zero_measure_extraction

end Zeta23.OPICAFollowup.IndependentCompactExtraction
