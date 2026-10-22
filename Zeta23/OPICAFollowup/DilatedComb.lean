import Zeta23.OPICAFollowup.ComplexLocalMeasures
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
UNCHECKED actual scaled integer-comb construction. The positive measure is a
push-forward of counting measure with its real amplitude. Temperateness is
proved from point counts, rather than attached as an unproved packet field.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology FourierTransform SchwartzMap ENNReal
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup

def scaledLatticePoint (t : ℝ) (n : ℤ) : ℝ := Real.exp t*(n:ℝ)
def scaledLatticeMeasure (t : ℝ) : Measure ℝ :=
  Measure.map (scaledLatticePoint t) (Measure.count : Measure ℤ)
def dilatedCombMeasure (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (Real.exp (t/2)) • scaledLatticeMeasure t

lemma scaledLatticePoint_measurable (t : ℝ) : Measurable (scaledLatticePoint t) :=
  measurable_from_countable _

lemma scaledLatticePoint_injective (t : ℝ) : Function.Injective (scaledLatticePoint t) := by
  intro m n h
  apply Int.cast_injective (R := ℝ)
  exact mul_left_cancel₀ (Real.exp_ne_zero t) h

lemma scaledLattice_preimage_bound (t R : ℝ) (hR : 0≤R) :
    (scaledLatticePoint t) ⁻¹' Icc (-R) R ⊆
      (↑(Finset.Icc (-(Nat.ceil (R/Real.exp t):ℤ)) (Nat.ceil (R/Real.exp t):ℤ)) : Set ℤ) := by
  intro n hn
  have hx : |(n:ℝ)|≤R/Real.exp t := by
    apply (le_div_iff₀ (Real.exp_pos t)).mpr
    have h := abs_le.mpr hn
    simpa only [scaledLatticePoint,abs_mul,abs_of_pos (Real.exp_pos t),mul_comm] using h
  have hc := Nat.le_ceil (R/Real.exp t)
  have hnx : |(n:ℝ)|≤(Nat.ceil (R/Real.exp t):ℝ) := hx.trans hc
  have h := abs_le.mp hnx
  simp only [Finset.mem_coe,Finset.mem_Icc]
  constructor <;> exact_mod_cast (by first | exact h.1 | exact h.2)

lemma scaledLattice_integer_box_card (N : ℕ) :
    (Finset.Icc (-(N:ℤ)) (N:ℤ)).card=2*N+1 := by
  rw [Int.card_Icc]
  omega

lemma scaledLatticeMeasure_interval_bound (t R : ℝ) (hR : 0≤R) :
    scaledLatticeMeasure t (Icc (-R) R) ≤
      ENNReal.ofReal (3+2*Real.exp (-t)*R) := by
  rw [scaledLatticeMeasure,Measure.map_apply (scaledLatticePoint_measurable t) measurableSet_Icc]
  have hcount := measure_mono (μ := (Measure.count : Measure ℤ)) (scaledLattice_preimage_bound t R hR)
  rw [Measure.count_apply_finset,scaledLattice_integer_box_card] at hcount
  apply hcount.trans
  have hceil : (Nat.ceil (R/Real.exp t):ℝ)<R/Real.exp t+1 := Nat.ceil_lt_add_one (by positivity)
  have hreal : ((2*Nat.ceil (R/Real.exp t)+1:ℕ):ℝ)≤3+2*Real.exp (-t)*R := by
    rw [Real.exp_neg]
    push_cast
    nlinarith
  exact_mod_cast (ENNReal.ofReal_le_ofReal hreal)

instance scaledLatticeMeasure_locallyFinite (t : ℝ) : IsLocallyFiniteMeasure (scaledLatticeMeasure t) where
  finiteAtNhds x := by
    let R := |x|+1
    refine ⟨Ioo (-R) R,Ioo_mem_nhds (by dsimp [R]; linarith [neg_le_abs x])
      (by dsimp [R]; linarith [le_abs_self x]),?_⟩
    exact (measure_mono Ioo_subset_Icc_self).trans_lt
      ((scaledLatticeMeasure_interval_bound t R (by dsimp [R]; positivity)).trans_lt ENNReal.ofReal_lt_top)

lemma scaledLatticeMeasure_linearGrowth (t : ℝ) : LinearMassGrowth (scaledLatticeMeasure t) := by
  refine ⟨3+2*Real.exp (-t),by positivity,fun R hR => ?_⟩
  have h := scaledLatticeMeasure_interval_bound t R hR
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  change (scaledLatticeMeasure t (Icc (-R) R)).toReal≤_
  nlinarith [Real.exp_pos (-t)]

instance dilatedCombMeasure_locallyFinite (t : ℝ) : IsLocallyFiniteMeasure (dilatedCombMeasure t) := by
  unfold dilatedCombMeasure
  infer_instance

lemma dilatedCombMeasure_linearGrowth (t : ℝ) : LinearMassGrowth (dilatedCombMeasure t) := by
  obtain ⟨C,hC,hbound⟩ := scaledLatticeMeasure_linearGrowth t
  refine ⟨Real.exp (t/2)*C,by positivity,fun R hR => ?_⟩
  unfold dilatedCombMeasure
  rw [measureReal_def,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (hbound R hR) (Real.exp_nonneg _)).trans_eq (by ring)

/-- Canonical real Jordan carrier; the negative part is zero. -/
def dilatedCombJordan (t : ℝ) : LocallyFiniteSignedMeasure :=
  localJordanDifference (dilatedCombMeasure t) 0

lemma dilatedCombJordan_growth (t : ℝ) : (dilatedCombJordan t).HasLinearGrowth := by
  simpa [dilatedCombJordan,localJordanDifference,LocallyFiniteSignedMeasure.totalVariation]
    using dilatedCombMeasure_linearGrowth t

def dilatedCombDistribution (t : ℝ) : TemperedDistribution ℝ ℂ :=
  (dilatedCombJordan t).distributionOfLinearGrowth (dilatedCombJordan_growth t)

lemma scaledLatticeMeasure_integrable_schwartz (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    Integrable f (scaledLatticeMeasure t) := by
  letI := hasTemperateGrowth_of_linear_growth _ (scaledLatticeMeasure_linearGrowth t)
  exact f.integrable

lemma dilatedComb_schwartz_summable (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => f (Real.exp t*(n:ℝ))) := by
  have hf := scaledLatticeMeasure_integrable_schwartz t f
  have hm := (integrable_map_measure hf.aestronglyMeasurable
    (scaledLatticePoint_measurable t).aemeasurable).mp hf
  have hs : Summable (fun n : ℤ => ‖f (Real.exp t*(n:ℝ))‖) := by
    simpa only [scaledLatticePoint,integrable_count_iff] using hm
  exact hs.of_norm

lemma dilatedCombDistribution_apply (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    dilatedCombDistribution t f=(Real.exp (t/2):ℂ)*∑' n : ℤ, f (Real.exp t*(n:ℝ)) := by
  rw [dilatedCombDistribution,LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
  simp only [dilatedCombJordan,localJordanDifference,Measure.sub_zero,zero_sub,
    integral_zero_measure,sub_zero,dilatedCombMeasure,integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [scaledLatticeMeasure,integral_map (scaledLatticePoint_measurable t).aemeasurable
    f.continuous.aestronglyMeasurable]
  have hc : Integrable (fun n : ℤ => f (scaledLatticePoint t n)) Measure.count := by
    apply (integrable_map_measure f.continuous.aestronglyMeasurable
      (scaledLatticePoint_measurable t).aemeasurable).mp
    exact scaledLatticeMeasure_integrable_schwartz t f
  rw [integral_countable hc]
  simp only [count_real_singleton,one_smul,scaledLatticePoint,RCLike.real_smul_eq_coe_mul]

lemma fourier_positive_scale (f : ℝ→ℂ) (a xi : ℝ) (ha : 0<a) :
    𝓕 (fun x : ℝ => f (a*x)) xi=(a⁻¹:ℝ) • 𝓕 f (xi/a) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  let F : ℝ→ℂ := fun x => Complex.exp (((-2*Real.pi*x*(xi/a)):ℝ)*Complex.I)*f x
  have heq : (fun x : ℝ => Complex.exp (((-2*Real.pi*x*xi):ℝ)*Complex.I)*f (a*x))=
      fun x => F (a*x) := by
    funext x
    dsimp [F]
    congr 2
    push_cast
    field_simp
    ring
  simp only [smul_eq_mul]
  rw [heq,Measure.integral_comp_mul_left F a,abs_inv,abs_of_pos ha]

lemma schwartz_scaled_decay_two (f : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0<a) :
    (fun x : ℝ => f (a*x)) =O[cocompact ℝ] (fun x : ℝ => |x|^(-2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := f.decay 2 0
  simp only [norm_iteratedFDeriv_zero] at hbound
  refine ⟨C/a^2,?_⟩
  filter_upwards [Filter.cocompact_le_cofinite (Filter.eventually_cofinite_ne (0:ℝ))] with x hx
  have hxpos : 0<|x| := abs_pos.mpr hx
  have h := hbound (a*x)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos ha,mul_pow] at h
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _),
    Real.rpow_neg (abs_nonneg x),Real.rpow_two]
  have ha0 := ha.ne'
  have hx0 := hxpos.ne'
  field_simp [ha0,hx0] at h ⊢
  nlinarith

lemma scaled_poisson_schwartz (f : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0<a) :
    (∑' n : ℤ, f (a*(n:ℝ)))=(a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)/a) := by
  have hf : Continuous (fun x : ℝ => f (a*x)) := f.continuous.comp (continuous_const.mul continuous_id)
  have hsum : Summable (fun n : ℤ => 𝓕 (fun x : ℝ => f (a*x)) n) := by
    simp_rw [fourier_positive_scale _ _ _ ha]
    have h := dilatedComb_schwartz_summable (-Real.log a) (𝓕 f)
    rw [Real.exp_neg,Real.exp_log ha] at h
    simpa only [div_eq_mul_inv,mul_comm] using h.const_smul a⁻¹
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hf
    (by norm_num : (1:ℝ)<2) (schwartz_scaled_decay_two f a ha) hsum 0
  simp only [zero_add,fourier_coe_apply,ofReal_zero,mul_zero,zero_mul,
    Complex.exp_zero,mul_one] at h
  rw [h]
  simp_rw [fourier_positive_scale _ _ _ ha]
  exact tsum_const_smul

/-- Full original comb root: true positive point-counting measure, genuine
Schwartz absolute convergence, exact amplitude and Fourier reflection t↦-t. -/
theorem dilated_comb_fourier (t : ℝ) :
    (∀ R : ℝ, 0≤R → dilatedCombMeasure t (Icc (-R) R)≤
      ENNReal.ofReal (Real.exp (t/2)*(3+2*Real.exp (-t)*R))) ∧
    (∀ f : SchwartzMap ℝ ℂ, Summable (fun n : ℤ => f (Real.exp t*(n:ℝ))) ∧
      dilatedCombDistribution t f=(Real.exp (t/2):ℂ)*∑' n : ℤ, f (Real.exp t*(n:ℝ))) ∧
    𝓕 (dilatedCombDistribution t)=dilatedCombDistribution (-t) := by
  refine ⟨?_,fun f => ⟨dilatedComb_schwartz_summable t f,dilatedCombDistribution_apply t f⟩,?_⟩
  · intro R hR
    rw [dilatedCombMeasure,Measure.smul_apply,smul_eq_mul,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul_left' (scaledLatticeMeasure_interval_bound t R hR) _
  · ext f
    change dilatedCombDistribution t (𝓕 f)=dilatedCombDistribution (-t) f
    rw [dilatedCombDistribution_apply,dilatedCombDistribution_apply]
    have h := scaled_poisson_schwartz f (Real.exp (-t)) (Real.exp_pos _)
    simp only [Real.exp_neg,inv_inv,div_inv_eq_mul,mul_comm (Real.exp t)] at h
    rw [h]
    simp only [RCLike.real_smul_eq_coe_mul,mul_assoc]
    congr 1
    rw [←Complex.ofReal_mul,←Real.exp_add]
    congr 2
    ring

end Zeta23.OPICAFollowup
