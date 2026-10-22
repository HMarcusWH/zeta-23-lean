import Zeta23.OPICAFollowup.ComplexLocalMeasures
import Zeta23.OPICA.SincTriangle
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
Actual scaled integer-comb construction. The positive measure is a
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
  measurable_of_countable _

lemma scaledLatticePoint_injective (t : ℝ) : Function.Injective (scaledLatticePoint t) := by
  intro m n h
  apply Int.cast_injective (α := ℝ)
  exact mul_left_cancel₀ (Real.exp_ne_zero t) h

/-- The exact mass of every physical atom of the scaled integer
counting measure. Noncompact global mass is immaterial to a singleton. -/
theorem scaledLatticeMeasure_atom (t : ℝ) (n : ℤ) :
    scaledLatticeMeasure t ({scaledLatticePoint t n} : Set ℝ) = 1 := by
  rw [scaledLatticeMeasure,
    Measure.map_apply (scaledLatticePoint_measurable t)
      (measurableSet_singleton _)]
  have hpre :
      (scaledLatticePoint t) ⁻¹'
        ({scaledLatticePoint t n} : Set ℝ) = ({n} : Set ℤ) := by
    ext m
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact scaledLatticePoint_injective t
    · rintro rfl
      rfl
  rw [hpre]
  simp

/-- The full positive dilated comb has the exact source amplitude at every
genuine lattice point. This is the atomic input for CT1 nonvanishing. -/
theorem dilatedCombMeasure_atom (t : ℝ) (n : ℤ) :
    dilatedCombMeasure t ({scaledLatticePoint t n} : Set ℝ) =
      ENNReal.ofReal (Real.exp (t / 2)) := by
  rw [dilatedCombMeasure, Measure.smul_apply, scaledLatticeMeasure_atom]
  simp

/-- The first nonzero positive atom is genuinely present. -/
theorem dilatedCombMeasure_first_positive_atom (t : ℝ) :
    dilatedCombMeasure t ({Real.exp t} : Set ℝ) =
      ENNReal.ofReal (Real.exp (t / 2)) := by
  simpa only [scaledLatticePoint, Int.cast_one, mul_one] using
    dilatedCombMeasure_atom t (1 : ℤ)

/-! ## Genuine first-cell support gap

The only lattice point in (-exp(t), exp(t)) is zero. These lemmas
use the actual mapped counting measure, not a synthetic gap witness.
All measure bounds apply to the full noncompact counting carrier. -/

/-- The integer indexing an actual scaled lattice point lying strictly
between the two first nonzero lattice points is necessarily zero. -/
theorem scaledLatticePoint_in_first_gap (t : ℝ) (n : ℤ)
    (hn : scaledLatticePoint t n ∈ Ioo (-Real.exp t) (Real.exp t)) :
    n = 0 := by
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have hlo : Real.exp t * (-1 : ℝ) < Real.exp t * (n : ℝ) := by
    simpa [scaledLatticePoint] using hn.1
  have hhi : Real.exp t * (n : ℝ) < Real.exp t * (1 : ℝ) := by
    simpa [scaledLatticePoint] using hn.2
  have hnlo : (-1 : ℝ) < (n : ℝ) := (mul_lt_mul_left hpos).mp hlo
  have hnhi : (n : ℝ) < (1 : ℝ) := (mul_lt_mul_left hpos).mp hhi
  have hloZ : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hhiZ : n < (1 : ℤ) := by exact_mod_cast hnhi
  omega

/-- The actual scaled counting measure assigns zero mass to the
first-cell punctured interval, even though it has an origin atom. -/
theorem scaledLatticeMeasure_punctured_gap (t : ℝ) :
    scaledLatticeMeasure t (Ioo (-Real.exp t) (Real.exp t) \ ({0} : Set ℝ)) =
      0 := by
  rw [scaledLatticeMeasure,
    Measure.map_apply (scaledLatticePoint_measurable t)
      (measurableSet_Ioo.diff (measurableSet_singleton 0))]
  have hempty : (scaledLatticePoint t) ⁻¹'
      (Ioo (-Real.exp t) (Real.exp t) \ ({0} : Set ℝ)) = ∅ := by
    ext n
    constructor
    · intro hn
      have hzero : n = 0 := scaledLatticePoint_in_first_gap t n hn.1
      exact hn.2 (by simp [scaledLatticePoint,hzero])
    · intro hn
      exact False.elim (Set.not_mem_empty n hn)
  rw [hempty]
  simp

/-- The complete positive dilated comb has the same punctured gap.
Its positive real amplitude never creates new support. -/
theorem dilatedCombMeasure_punctured_gap (t : ℝ) :
    dilatedCombMeasure t (Ioo (-Real.exp t) (Real.exp t) \ ({0} : Set ℝ)) =
      0 := by
  rw [dilatedCombMeasure, Measure.smul_apply,
    scaledLatticeMeasure_punctured_gap]
  simp

/-- Any smaller punctured first-cell interval is also mass-free. -/
theorem dilatedCombMeasure_punctured_gap_of_le (t a : ℝ)
    (ha : a ≤ Real.exp t) :
    dilatedCombMeasure t (Ioo (-a) a \ ({0} : Set ℝ)) = 0 := by
  apply measure_mono_null ?_ (dilatedCombMeasure_punctured_gap t)
  intro x hx
  exact ⟨⟨lt_of_le_of_lt (neg_le_neg ha) hx.1.1,
    lt_of_lt_of_le hx.1.2 ha⟩, hx.2⟩

lemma scaledLattice_preimage_bound (t R : ℝ) (_hR : 0≤R) :
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
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

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
    rw [div_eq_mul_inv] at hceil
    rw [div_eq_mul_inv]
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
  have := IsFiniteMeasureOnCompacts.smul (scaledLatticeMeasure t)
    (c := ENNReal.ofReal (Real.exp (t/2))) ENNReal.ofReal_ne_top
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
  simpa [dilatedCombJordan,localJordanDifference,LocallyFiniteSignedMeasure.HasLinearGrowth,
    LocallyFiniteSignedMeasure.totalVariation,Measure.zero_sub]
    using dilatedCombMeasure_linearGrowth t

def dilatedCombDistribution (t : ℝ) : TemperedDistribution ℝ ℂ :=
  (dilatedCombJordan t).distributionOfLinearGrowth (dilatedCombJordan_growth t)

lemma scaledLatticeMeasure_integrable_schwartz (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    Integrable f (scaledLatticeMeasure t) := by
  have := hasTemperateGrowth_of_linear_growth _ (scaledLatticeMeasure_linearGrowth t)
  exact f.integrable

lemma dilatedComb_schwartz_summable (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => f (Real.exp t*(n:ℝ))) := by
  have hf := scaledLatticeMeasure_integrable_schwartz t f
  have hm := (integrable_map_measure hf.aestronglyMeasurable
    (scaledLatticePoint_measurable t).aemeasurable).mp hf
  have hs : Summable (fun n : ℤ => ‖f (Real.exp t*(n:ℝ))‖) := by
    simpa only [Function.comp_def,scaledLatticePoint,integrable_count_iff] using hm
  exact hs.of_norm

lemma dilatedCombDistribution_apply (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    dilatedCombDistribution t f=(Real.exp (t/2):ℂ)*∑' n : ℤ, f (Real.exp t*(n:ℝ)) := by
  rw [dilatedCombDistribution,LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
  simp only [dilatedCombJordan,localJordanDifference,Measure.sub_zero,Measure.zero_sub,
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
  rfl

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
    field_simp [ha.ne', Complex.ofReal_ne_zero.mpr ha.ne']
  simp only [smul_eq_mul]
  rw [heq,Measure.integral_comp_mul_left F a,abs_inv,abs_of_pos ha]

/-- Positive dilation acts on genuine Schwartz functions by a continuous linear equivalence. -/
def schwartzPositiveScale (a : ℝ) (ha : 0<a) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a ha.ne')) f

lemma schwartzPositiveScale_apply (a : ℝ) (ha : 0<a) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzPositiveScale a ha f x=f (a*x) := by
  simp [schwartzPositiveScale,mul_comm]

lemma scaled_poisson_schwartz (f : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0<a) :
    (∑' n : ℤ, f (a*(n:ℝ)))=(a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)/a) := by
  let g := schwartzPositiveScale a ha f
  have hg : (g : ℝ→ℂ) = fun x => f (a*x) := by
    funext x
    exact schwartzPositiveScale_apply a ha f x
  have hfourier (x : ℝ) : (𝓕 g) x=(a⁻¹:ℝ) • (𝓕 f) (x/a) := by
    rw [SchwartzMap.fourier_coe,hg,fourier_positive_scale _ _ _ ha]
    rfl
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add,hfourier,AddCircle.coe_zero,fourier_eval_zero,mul_one] at h
  simpa only [g,schwartzPositiveScale_apply,tsum_const_smul''] using h

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
    exact mul_le_mul_right (scaledLatticeMeasure_interval_bound t R hR) _
  · ext f
    change dilatedCombDistribution t (𝓕 f)=dilatedCombDistribution (-t) f
    rw [dilatedCombDistribution_apply,dilatedCombDistribution_apply]
    have h := scaled_poisson_schwartz f (Real.exp (-t)) (Real.exp_pos _)
    have hi : (Real.exp (-t))⁻¹=Real.exp t := by rw [Real.exp_neg,inv_inv]
    have hd (n : ℤ) : (n:ℝ)/Real.exp (-t)=Real.exp t*(n:ℝ) := by
      rw [div_eq_mul_inv,hi,mul_comm]
    simp only [hi,hd] at h
    rw [h]
    simp only [RCLike.real_smul_eq_coe_mul]
    have he : Real.exp (t/2)=Real.exp (-t/2)*Real.exp t := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he,Complex.ofReal_mul]
    exact mul_assoc (Real.exp (-t/2) : ℂ) (Real.exp t : ℂ)
      (∑' n : ℤ, (𝓕 f) (Real.exp t*(n:ℝ)))

/-- The planned public comb interface is the actual positive lattice distribution. -/
abbrev dilatedComb (t : ℝ) : TemperedDistribution ℝ ℂ := dilatedCombDistribution t

/-- Its physical Schwartz pairing, with the prescribed heat amplitude. -/
def combPairing (t : ℝ) (f : SchwartzMap ℝ ℂ) : ℂ :=
  (Real.exp (t/2):ℂ)*∑' n : ℤ, f (Real.exp t*(n:ℝ))

theorem dilatedComb_apply (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    dilatedComb t f=combPairing t f := dilatedCombDistribution_apply t f

/-- The origin atom has the prescribed amplitude for every real dilation. -/
theorem dilatedCombMeasure_origin (t : ℝ) :
    dilatedCombMeasure t ({0} : Set ℝ)=ENNReal.ofReal (Real.exp (t/2)) := by
  rw [dilatedCombMeasure,Measure.smul_apply,scaledLatticeMeasure,
    Measure.map_apply (scaledLatticePoint_measurable t) (measurableSet_singleton 0)]
  have hpre : scaledLatticePoint t ⁻¹' ({0} : Set ℝ)=({0} : Set ℤ) := by
    ext n
    simp [scaledLatticePoint,Real.exp_ne_zero]
  rw [hpre]
  simp

end Zeta23.OPICAFollowup
