import Zeta23.OPICAFollowup.ZeroProfiles
import Zeta23.OPICA.Involution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
The nonlinear square and its Fourier defect (R2-S3). Let h ∈ L¹ ∩ L² be even, continuous,
Fourier self-dual (𝓕h = h), vanishing at infinity, with h = A on [-1, 1]. The actual zero profile
is such an h, with A = 1. Put τ_h = |A - h|² dx - |A|² Σ_(n ≠ 0) δ_n, paired with Schwartz tests.

- 𝓕(|h|²) = h ⋆ conj h by the multiplication formula, using 𝓕(conj h) = conj h. Poisson
  summation interchanges the constant and comb terms with the matching origin terms, giving
  𝓕τ_h - τ_h = d dx with the real C₀ defect d = h ⋆ conj h - |h|² (S3.1). Evenness gives
  d(0) = ‖h‖₂² - |A|² > 0 (S3.2).
- No tempered lattice-supported correction σ = Σ c_n δ_n repairs the defect. Translating a test by
  one does not change its Fourier transform at the integers, so d(x+1) - d(x) annihilates every
  test supported off the lattice. Hence d is 1-periodic, therefore zero, which contradicts
  d(0) > 0.
- The self-dual projection (τ + 𝓕τ)/2, the parent `Zeta23.OPICA.involutionSelfdualProjection`
  for the Fourier action on functionals, equals τ + d/2 dx. Its density is strictly positive on
  an interval about 0 inside the old gap.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ComplexConjugate Real ContDiff

namespace Zeta23.OPICAFollowup

section Autocorrelation

/-- The autocorrelation (h ⋆ conj h)(x) = ∫ h(y) conj h(x - y) dy. -/
def autocorr (h : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, h y * conj (h (x - y))

lemma fourier_conj_of_selfdual {h : ℝ → ℂ} (hsd : 𝓕 h = h) (hev : ∀ x, h (-x) = h x) (η : ℝ) :
    𝓕 (fun x => conj (h x)) η = conj (h η) := by
  rw [Real.fourier_real_eq]
  have : (∫ v : ℝ, 𝐞 (-(v * η)) • conj (h v)) = conj (∫ v : ℝ, 𝐞 (-(v * -η)) • h v) := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul, map_mul, Real.fourierChar_apply, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast; ring
  rw [this, ← Real.fourier_real_eq, hsd, hev]

/-- For an even self-dual integrable h, 𝓕(|h|²) = h ⋆ conj h. -/
theorem fourier_normSq_eq_autocorr {h : ℝ → ℂ} (hint : Integrable h) (hsd : 𝓕 h = h)
    (hev : ∀ x, h (-x) = h x) (ξ : ℝ) :
    𝓕 (fun x => h x * conj (h x)) ξ = autocorr h ξ := by
  have hc : Integrable (fun x => conj (h x)) :=
    memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hint).star
  set g : ℝ → ℂ := fun x => conj (h x) * (𝐞 (-(x * ξ)) : ℂ) with hg
  have hec : Continuous (fun x : ℝ => ((𝐞 (-(x * ξ)) : Circle) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const).neg)
  have hgi : Integrable g :=
    hc.mul_bdd hec.aestronglyMeasurable (Eventually.of_forall fun x => le_of_eq (Circle.norm_coe _))
  have step1 : 𝓕 (fun x => h x * conj (h x)) ξ = ∫ x, 𝓕 h x * g x := by
    rw [Real.fourier_real_eq, hsd]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Circle.smul_def, smul_eq_mul, hg]; ring
  have step2 : ∀ y, 𝓕 g y = conj (h (y + ξ)) := by
    intro y
    rw [← fourier_conj_of_selfdual hsd hev, Real.fourier_real_eq, Real.fourier_real_eq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have he : ((𝐞 (-(x * y)) : Circle) : ℂ) * (𝐞 (-(x * ξ)) : Circle) = (𝐞 (-(x * (y + ξ))) : Circle) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; congr 2; ring
    simp only [Circle.smul_def, smul_eq_mul, hg]
    rw [← he]; ring
  rw [step1, integral_fourier_mul_eq_of_integrable hint hgi, autocorr]
  simp_rw [step2]
  rw [← integral_neg_eq_self (fun y => h y * conj (h (y + ξ)))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hev]; ring_nf

end Autocorrelation

section Defect

/-- τ_h = |A - h|² dx - |A|² Σ_(n ≠ 0) δ_n, paired with Schwartz tests. -/
def squareGapMeasure (h : ℝ → ℂ) (A : ℂ) (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  (∫ x, ((‖A - h x‖ ^ 2 : ℝ) : ℂ) * φ x) - ((‖A‖ ^ 2 : ℝ) : ℂ) * ∑' n : ℤ, (if n = 0 then 0 else φ n)

/-- The Fourier defect density d = h ⋆ conj h - |h|². -/
def squareDualityDefect (h : ℝ → ℂ) (x : ℝ) : ℂ := autocorr h x - h x * conj (h x)

lemma comb_summable (φ : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => φ n) := by
  have := ((dilated_comb_fourier 0).2.1 φ).1
  simpa using this

lemma comb_fourier (φ : 𝓢(ℝ, ℂ)) : ∑' n : ℤ, (𝓕 φ : 𝓢(ℝ, ℂ)) n = ∑' n : ℤ, φ n := by
  have h1 := ((dilated_comb_fourier 0).2.1 (𝓕 φ)).2
  have h2 := ((dilated_comb_fourier 0).2.1 φ).2
  have h3 := dilatedCombDistribution_zero_fourier φ
  rw [h1, h2] at h3
  simpa using h3

lemma tsum_punctured {ψ : ℤ → ℂ} (hψ : Summable ψ) :
    ∑' n : ℤ, (if n = 0 then 0 else ψ n) = (∑' n : ℤ, ψ n) - ψ 0 := by
  have hs : Summable (fun n : ℤ => if n = 0 then ψ 0 else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro n hn; simp at hn; simp [hn])
  have e : (fun n : ℤ => if n = 0 then 0 else ψ n) = fun n => ψ n - if n = 0 then ψ 0 else 0 := by
    funext n; split_ifs with h <;> simp [h]
  rw [e, hψ.tsum_sub hs, tsum_ite_eq]

lemma normSq_sub_expand (A z : ℂ) : ((‖A - z‖ ^ 2 : ℝ) : ℂ) =
    ((‖A‖ ^ 2 : ℝ) : ℂ) - A * conj z - conj A * z + z * conj z := by
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj', map_sub]; ring

end Defect

section DefectIdentity

variable {h : ℝ → ℂ}

lemma schwartz_bdd (φ : 𝓢(ℝ, ℂ)) : ∃ C, ∀ x, ‖φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := φ.decay 0 0
  exact ⟨C, fun x => by simpa using hC.2 x⟩

lemma square_integrable_mul_schwartz {f : ℝ → ℂ} (hf : Integrable f) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => f x * φ x) := by
  obtain ⟨C, hC⟩ := schwartz_bdd φ
  exact hf.mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall hC)

lemma integrable_conj' (hint : Integrable h) : Integrable (fun x => conj (h x)) :=
  memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hint).star

lemma integrable_normSq (hL2 : MemLp h 2) : Integrable (fun x => h x * conj (h x)) := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
  exact hL2.integrable_mul hL2.star

lemma autocorr_eq_fourier (hint : Integrable h) (hsd : 𝓕 h = h) (hev : ∀ x, h (-x) = h x) :
    autocorr h = 𝓕 (fun x => h x * conj (h x)) :=
  funext fun ξ => (fourier_normSq_eq_autocorr hint hsd hev ξ).symm

lemma integrable_autocorr_mul (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hev : ∀ x, h (-x) = h x) (φ : 𝓢(ℝ, ℂ)) : Integrable (fun x => autocorr h x * φ x) := by
  rw [autocorr_eq_fourier hint hsd hev]
  obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖𝓕 (fun x => h x * conj (h x)) t‖ ≤ C :=
    ⟨_, fun t => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ t⟩
  exact φ.integrable.bdd_mul (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner (integrable_normSq hL2)).aestronglyMeasurable (Eventually.of_forall hC)

/-- (S3.1): 𝓕τ_h - τ_h = (h ⋆ conj h - |h|²) dx on Schwartz tests. -/
theorem squareGapMeasure_fourier_defect (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hev : ∀ x, h (-x) = h x) (A : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    squareGapMeasure h A (𝓕 φ) - squareGapMeasure h A φ = ∫ x, squareDualityDefect h x * φ x := by
  have hc := integrable_conj' hint
  have hN := integrable_normSq hL2
  have hF : ∀ ψ : 𝓢(ℝ, ℂ), (∫ x, ((‖A - h x‖ ^ 2 : ℝ) : ℂ) * ψ x) =
      ((‖A‖ ^ 2 : ℝ) : ℂ) * (∫ x, ψ x) - A * (∫ x, conj (h x) * ψ x) - conj A * (∫ x, h x * ψ x) +
        ∫ x, h x * conj (h x) * ψ x := by
    intro ψ
    have i1 : Integrable (fun x => ((‖A‖ ^ 2 : ℝ) : ℂ) * ψ x) := ψ.integrable.const_mul _
    have i2 : Integrable (fun x => A * (conj (h x) * ψ x)) := (square_integrable_mul_schwartz hc ψ).const_mul _
    have i3 : Integrable (fun x => conj A * (h x * ψ x)) := (square_integrable_mul_schwartz hint ψ).const_mul _
    have i4 : Integrable (fun x => h x * conj (h x) * ψ x) := square_integrable_mul_schwartz hN ψ
    have e : (fun x => ((‖A - h x‖ ^ 2 : ℝ) : ℂ) * ψ x) = fun x =>
        ((‖A‖ ^ 2 : ℝ) : ℂ) * ψ x - A * (conj (h x) * ψ x) - conj A * (h x * ψ x) +
          h x * conj (h x) * ψ x := funext fun x => by rw [normSq_sub_expand]; ring
    rw [e, integral_add (f := fun x => ((‖A‖ ^ 2 : ℝ) : ℂ) * ψ x - A * (conj (h x) * ψ x) -
        conj A * (h x * ψ x)) (g := fun x => h x * conj (h x) * ψ x) ((i1.sub i2).sub i3) i4,
      integral_sub (f := fun x => ((‖A‖ ^ 2 : ℝ) : ℂ) * ψ x - A * (conj (h x) * ψ x))
        (g := fun x => conj A * (h x * ψ x)) (i1.sub i2) i3,
      integral_sub i1 i2, integral_const_mul, integral_const_mul, integral_const_mul]
  have hmul : ∀ f : ℝ → ℂ, Integrable f → (∫ x, f x * (𝓕 φ : 𝓢(ℝ, ℂ)) x) = ∫ x, 𝓕 f x * φ x := by
    intro f hf
    rw [SchwartzMap.fourier_coe, integral_fourier_mul_eq_of_integrable hf φ.integrable]
  have hconjF : 𝓕 (fun x => conj (h x)) = fun x => conj (h x) :=
    funext (fourier_conj_of_selfdual hsd hev)
  rw [squareGapMeasure, squareGapMeasure, hF, hF, hmul _ hc, hmul _ hint, hmul _ hN, hconjF, hsd,
    ← autocorr_eq_fourier hint hsd hev, schwartz_integral_fourier,
    tsum_punctured (comb_summable (𝓕 φ)), tsum_punctured (comb_summable φ), comb_fourier,
    Int.cast_zero, schwartz_fourier_zero]
  have i5 := integrable_autocorr_mul hint hL2 hsd hev φ
  have i6 : Integrable (fun x => h x * conj (h x) * φ x) := square_integrable_mul_schwartz hN φ
  rw [show (∫ x, squareDualityDefect h x * φ x) = (∫ x, autocorr h x * φ x) - ∫ x, h x * conj (h x) * φ x by
    rw [← integral_sub i5 i6]; exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only [squareDualityDefect]; ring)]
  push_cast
  ring

end DefectIdentity

section DefectProperties

variable {h : ℝ → ℂ}

lemma continuous_squareDualityDefect (hcont : Continuous h) (hint : Integrable h) (hL2 : MemLp h 2)
    (hsd : 𝓕 h = h) (hev : ∀ x, h (-x) = h x) : Continuous (squareDualityDefect h) := by
  have hc : Continuous (autocorr h) := by
    rw [autocorr_eq_fourier hint hsd hev]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      (integrable_normSq hL2)
  exact hc.sub (hcont.mul (Complex.continuous_conj.comp hcont))

lemma tendsto_squareDualityDefect (hint : Integrable h) (hsd : 𝓕 h = h) (hev : ∀ x, h (-x) = h x)
    (hvan : Tendsto h (cocompact ℝ) (𝓝 0)) : Tendsto (squareDualityDefect h) (cocompact ℝ) (𝓝 0) := by
  have h1 : Tendsto (autocorr h) (cocompact ℝ) (𝓝 0) := by
    rw [autocorr_eq_fourier hint hsd hev]; exact Real.zero_at_infty_fourier _
  have h2 : Tendsto (fun x => h x * conj (h x)) (cocompact ℝ) (𝓝 0) := by
    have := hvan.mul ((Complex.continuous_conj.tendsto 0).comp hvan)
    simpa using this
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  exact h3

/-- d is real-valued: conj (h ⋆ conj h)(x) = (h ⋆ conj h)(x). -/
lemma squareDualityDefect_im (x : ℝ) : (squareDualityDefect h x).im = 0 := by
  have hA : conj (autocorr h x) = autocorr h x := by
    rw [autocorr, ← integral_conj]
    have hs := integral_sub_left_eq_self (fun y => h y * conj (h (x - y))) (μ := volume) x
    rw [← hs]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [map_mul, Complex.conj_conj, sub_sub_cancel]; ring
  have hB : conj (h x * conj (h x)) = h x * conj (h x) := by
    simp only [map_mul, Complex.conj_conj]; ring
  have := congrArg Complex.im (show conj (squareDualityDefect h x) = squareDualityDefect h x by
    rw [squareDualityDefect, map_sub, hA, hB])
  simp only [Complex.conj_im] at this
  linarith

/-- d(0) = ‖h‖₂² - |A|². -/
lemma squareDualityDefect_zero (hev : ∀ x, h (-x) = h x) {A : ℂ} (hpl : ∀ x, |x| ≤ 1 → h x = A) :
    squareDualityDefect h 0 = (((∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 : ℝ) : ℂ) := by
  rw [squareDualityDefect, autocorr, hpl 0 (by simp)]
  have e1 : (∫ y, h y * conj (h (0 - y))) = ((∫ x, ‖h x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [zero_sub, hev]; push_cast; rw [Complex.mul_conj']
  rw [e1, Complex.mul_conj']; push_cast; ring

/-- ‖h‖₂² > |A|² for nonzero h (and ≥ 2|A|² from the plateau). -/
lemma norm_sq_gt (hcont : Continuous h) (hL2 : MemLp h 2) {A : ℂ}
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    ‖A‖ ^ 2 < ∫ x, ‖h x‖ ^ 2 ∧ 2 * ‖A‖ ^ 2 ≤ ∫ x, ‖h x‖ ^ 2 := by
  have hI : Integrable (fun x => ‖h x‖ ^ 2) := hL2.integrable_norm_pow (p := 2) two_ne_zero
  have hnn : ∀ x, 0 ≤ ‖h x‖ ^ 2 := fun x => sq_nonneg _
  have hplat : 2 * ‖A‖ ^ 2 ≤ ∫ x, ‖h x‖ ^ 2 := by
    have h1 : (∫ x in Icc (-1 : ℝ) 1, ‖h x‖ ^ 2) = 2 * ‖A‖ ^ 2 := by
      rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => ‖A‖ ^ 2) fun x hx => by
        simp only [hpl x (abs_le.mpr hx)]]
      rw [setIntegral_const, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]; ring
    rw [← h1]
    exact setIntegral_le_integral hI (Eventually.of_forall hnn)
  refine ⟨?_, hplat⟩
  by_cases hA : A = 0
  · subst hA
    obtain ⟨x0, hx0⟩ : ∃ x0, h x0 ≠ 0 := by
      by_contra hc; push Not at hc; exact hne (funext hc)
    have hpos : 0 < ‖h x0‖ ^ 2 := by positivity
    have hcn : Continuous (fun x => ‖h x‖ ^ 2) := (continuous_norm.comp hcont).pow 2
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcn x0 (‖h x0‖ ^ 2 / 2) (by positivity)
    have hlow : ∀ x ∈ Ioo (x0 - δ) (x0 + δ), ‖h x0‖ ^ 2 / 2 ≤ ‖h x‖ ^ 2 := by
      intro x hx
      have hd : dist x x0 < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
      have := hball x hd
      rw [Real.dist_eq, abs_lt] at this; linarith [this.1]
    have hmono : (∫ x in Ioo (x0 - δ) (x0 + δ), ‖h x0‖ ^ 2 / 2) ≤ ∫ x in Ioo (x0 - δ) (x0 + δ), ‖h x‖ ^ 2 :=
      setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hI.integrableOn measurableSet_Ioo hlow
    have hconst : (∫ x in Ioo (x0 - δ) (x0 + δ), ‖h x0‖ ^ 2 / 2) = 2 * δ * (‖h x0‖ ^ 2 / 2) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring
    have hsub : (∫ x in Ioo (x0 - δ) (x0 + δ), ‖h x‖ ^ 2) ≤ ∫ x, ‖h x‖ ^ 2 :=
      setIntegral_le_integral hI (Eventually.of_forall hnn)
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    nlinarith
  · have : 0 < ‖A‖ ^ 2 := by positivity
    linarith

end DefectProperties

section NoRepair

/-- A lattice-supported order-zero correction σ = Σ_n c_n δ_n, paired with Schwartz tests. -/
def latticePairing (c : ℤ → ℂ) (φ : 𝓢(ℝ, ℂ)) : ℂ := ∑' n : ℤ, c n * φ n

/-- Tempered (polynomially bounded) lattice weights. -/
def TemperedLatticeWeights (c : ℤ → ℂ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℤ, ‖c n‖ ≤ C * (1 + |(n : ℝ)|) ^ k

lemma fourierChar_int (n : ℤ) : ((𝐞 (n : ℝ) : Circle) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  push_cast; ring

/-- Translating a test by 1 does not change its Fourier transform at the integers. -/
lemma fourier_shift_int (g : ℝ → ℂ) (n : ℤ) :
    𝓕 (fun x => g (x - 1)) n = 𝓕 g n := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  rw [← integral_add_right_eq_self (fun x => 𝐞 (-(x * (n : ℝ))) • g (x - 1)) (1 : ℝ)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [add_sub_cancel_right, Circle.smul_def, smul_eq_mul]
  congr 1
  have : -((y + 1) * (n : ℝ)) = -(y * n) + -(n : ℝ) := by ring
  rw [this, AddChar.map_add_eq_mul, Circle.coe_mul, show (-(n : ℝ)) = ((-n : ℤ) : ℝ) by push_cast; ring,
    fourierChar_int, mul_one]

variable {h : ℝ → ℂ}

/-- No tempered lattice-supported correction repairs a nonzero defect value d(0). -/
theorem no_lattice_repair (hcont : Continuous h) (hint : Integrable h) (hL2 : MemLp h 2)
    (hsd : 𝓕 h = h) (hev : ∀ x, h (-x) = h x) (hvan : Tendsto h (cocompact ℝ) (𝓝 0)) (A : ℂ)
    (hd0 : squareDualityDefect h 0 ≠ 0) :
    ¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧ ∀ φ : 𝓢(ℝ, ℂ),
      squareGapMeasure h A (𝓕 φ) + latticePairing c (𝓕 φ) = squareGapMeasure h A φ + latticePairing c φ := by
  rintro ⟨c, -, hc⟩
  set d := squareDualityDefect h with hddef
  have hdc : Continuous d := continuous_squareDualityDefect hcont hint hL2 hsd hev
  have hdt : Tendsto d (cocompact ℝ) (𝓝 0) := tendsto_squareDualityDefect hint hsd hev hvan
  -- d is bounded
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖d x‖ ≤ M := by
    obtain ⟨K, hK, hKc⟩ : ∃ K : Set ℝ, IsCompact K ∧ ∀ x ∉ K, ‖d x‖ < 1 := by
      have := hdt (Metric.ball_mem_nhds 0 one_pos)
      rw [Filter.mem_map, Filter.mem_cocompact] at this
      obtain ⟨K, hK, hKs⟩ := this
      exact ⟨K, hK, fun x hx => by simpa using hKs hx⟩
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hdc.continuousOn
    exact ⟨max B 1, fun x => by
      by_cases hx : x ∈ K
      · exact (hB x hx).trans (le_max_left _ _)
      · exact (hKc x hx).le.trans (le_max_right _ _)⟩
  have key : ∀ φ : 𝓢(ℝ, ℂ), latticePairing c (𝓕 φ) = latticePairing c φ - ∫ x, d x * φ x := by
    intro φ
    have h1 := hc φ
    have h2 := squareGapMeasure_fourier_defect hint hL2 hsd hev A φ
    linear_combination h1 - h2
  set U : Set ℝ := (Set.range (fun n : ℤ => (n : ℝ)))ᶜ with hU
  have hUo : IsOpen U := by
    rw [hU, isOpen_compl_iff]
    exact (Int.isClosedEmbedding_coe_real.isClosed_range)
  set D : ℝ → ℂ := fun x => d (x + 1) - d x with hD
  have hDc : Continuous D := (hdc.comp (continuous_id.add continuous_const)).sub hdc
  have hint0 : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ → Integrable (fun x => d x * φ x) := by
    intro φ hφ hcs
    exact (hφ.integrable_of_hasCompactSupport hcs).bdd_mul hdc.aestronglyMeasurable
      (Eventually.of_forall hM)
  have hDzero : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • D x = 0 := by
    intro g hg hgc hgU
    set φ : ℝ → ℂ := fun x => (g x : ℂ) with hφ
    have hφs : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp hg
    have hφc : HasCompactSupport φ := hgc.comp_left Complex.ofReal_zero
    set ψ : ℝ → ℂ := fun x => φ (x - 1) with hψ
    have hψs : ContDiff ℝ ∞ ψ := hφs.comp (contDiff_id.sub contDiff_const)
    have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.subRight (1 : ℝ))
    have hφZ : ∀ n : ℤ, φ n = 0 := fun n => by
      have : (n : ℝ) ∉ tsupport g := fun hn => hgU hn ⟨n, rfl⟩
      simp [φ, image_eq_zero_of_notMem_tsupport this]
    have hψZ : ∀ n : ℤ, ψ n = 0 := fun n => by
      simp only [ψ, show (n : ℝ) - 1 = ((n - 1 : ℤ) : ℝ) by push_cast; ring, hφZ]
    set Φ : 𝓢(ℝ, ℂ) := hφc.toSchwartzMap hφs
    set Ψ : 𝓢(ℝ, ℂ) := hψc.toSchwartzMap hψs
    have hkΦ := key Φ
    have hkΨ := key Ψ
    have hl0 : ∀ χ : 𝓢(ℝ, ℂ), (∀ n : ℤ, χ n = 0) → latticePairing c χ = 0 := fun χ hχ => by
      simp [latticePairing, hχ]
    rw [hl0 Φ hφZ] at hkΦ
    rw [hl0 Ψ hψZ] at hkΨ
    have hsame : latticePairing c (𝓕 Ψ) = latticePairing c (𝓕 Φ) := by
      unfold latticePairing
      congr 1; funext n; congr 1
      simp only [SchwartzMap.fourier_coe]
      exact fourier_shift_int φ n
    have hI : (∫ x, d x * ψ x) = ∫ x, d (x + 1) * φ x := by
      rw [← integral_add_right_eq_self (fun x => d x * ψ x) (1 : ℝ)]
      simp only [ψ, add_sub_cancel_right]
    have heq : (∫ x, d (x + 1) * φ x) = ∫ x, d x * φ x := by
      have e1 : latticePairing c (𝓕 Ψ) = -∫ x, d x * Ψ x := by rw [hkΨ]; ring
      have e2 : latticePairing c (𝓕 Φ) = -∫ x, d x * Φ x := by rw [hkΦ]; ring
      have : (∫ x, d x * Ψ x) = ∫ x, d x * Φ x := by rw [← neg_inj, ← e1, ← e2, hsame]
      rw [← hI]; exact this
    have hi1 : Integrable (fun x => d (x + 1) * φ x) :=
      (hφs.continuous.integrable_of_hasCompactSupport hφc).bdd_mul
        (hdc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun x => hM _)
    have hi2 := hint0 φ hφs.continuous hφc
    calc ∫ x, g x • D x = ∫ x, d (x + 1) * φ x - d x * φ x := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hD, φ, Complex.real_smul]; ring
      _ = 0 := by rw [integral_sub hi1 hi2, heq, sub_self]
  have hae := hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hDc.locallyIntegrable.locallyIntegrableOn U) hDzero
  have hnull : (volume : Measure ℝ) (Set.range (fun n : ℤ => (n : ℝ))) = 0 :=
    (Set.countable_range _).measure_zero _
  have hae' : D =ᵐ[volume] 0 := by
    filter_upwards [hae, measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxU
    exact hx hxU
  have hDall : ∀ x, D x = 0 := fun x => congrFun ((hDc.ae_eq_iff_eq volume continuous_const).mp hae') x
  have hper : ∀ n : ℕ, d n = d 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hDall n
      simp only [hD, sub_eq_zero] at this
      push_cast; rw [this, ih]
  have hlim : Tendsto (fun n : ℕ => d n) atTop (𝓝 0) :=
    hdt.comp (tendsto_natCast_atTop_atTop.mono_right atTop_le_cocompact)
  have : d 0 = 0 := by
    have hconst : Tendsto (fun n : ℕ => d n) atTop (𝓝 (d 0)) :=
      tendsto_const_nhds.congr fun n => (hper n).symm
    exact tendsto_nhds_unique hconst hlim
  exact hd0 this

end NoRepair

section Projection

/-- The Fourier transform acting on Schwartz-test functionals: (𝓕T)(φ) = T(𝓕φ). -/
def fourierFunctional : (𝓢(ℝ, ℂ) → ℂ) →ₗ[ℂ] (𝓢(ℝ, ℂ) → ℂ) where
  toFun T := fun φ => T (𝓕 φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma fourier_fourier_schwartz (φ : 𝓢(ℝ, ℂ)) : 𝓕 (𝓕 φ) = schwartzReflect φ := by
  have h := SchwartzMap.fourierInv_apply_eq (𝓕 φ)
  rw [FourierTransform.fourierInv_fourier_eq] at h
  have h' : φ = schwartzReflect (𝓕 (𝓕 φ)) := h
  ext x
  calc (𝓕 (𝓕 φ)) x = (schwartzReflect (𝓕 (𝓕 φ))) (-x) := by rw [schwartzReflect_apply, neg_neg]
    _ = φ (-x) := by rw [← h']
    _ = schwartzReflect φ x := (schwartzReflect_apply φ x).symm

variable {h : ℝ → ℂ}

lemma squareGapMeasure_reflect (hev : ∀ x, h (-x) = h x) (A : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    squareGapMeasure h A (schwartzReflect φ) = squareGapMeasure h A φ := by
  rw [squareGapMeasure, squareGapMeasure]
  congr 1
  · rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [schwartzReflect_apply, neg_neg, hev]
  · congr 1
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [Equiv.neg_apply, neg_eq_zero, schwartzReflect_apply, Int.cast_neg, neg_neg]

lemma squareGapMeasure_gap {A : ℂ} (hpl : ∀ x, |x| ≤ 1 → h x = A) (φ : 𝓢(ℝ, ℂ))
    (hφ : tsupport φ ⊆ Ioo (-1) 1) : squareGapMeasure h A φ = 0 := by
  have hz : ∀ x, x ∉ Ioo (-1 : ℝ) 1 → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hφ h')
  rw [squareGapMeasure]
  have h1 : (∫ x, ((‖A - h x‖ ^ 2 : ℝ) : ℂ) * φ x) = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · simp [hpl x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)]
    · simp [hz x hx]
  have h2 : (∑' n : ℤ, (if n = 0 then 0 else φ n)) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    split_ifs with hn
    · rfl
    · refine hz _ fun hmem => hn ?_
      have h1 : (-1 : ℝ) < n := hmem.1
      have h2 : (n : ℝ) < 1 := hmem.2
      have : (-1 : ℤ) < n := by exact_mod_cast h1
      have : n < (1 : ℤ) := by exact_mod_cast h2
      omega
  rw [h1, h2, mul_zero, sub_zero]

end Projection

section Roots

variable {h : ℝ → ℂ} {A : ℂ}

/-- R2-S3: for an even continuous Fourier-self-dual h ∈ L¹ ∩ L² vanishing at infinity with h = A
on [-1, 1], the measure τ_h = |A - h|² dx - |A|² Σ_(n ≠ 0) δ_n has no origin atom and vanishes on
the open unit gap, has nonnegative off-lattice density and bounded density (linear variation
growth); its Fourier defect is the real continuous function d = h ⋆ conj h - |h|² vanishing at
infinity, with d = 𝓕(|h|²) - |h|², and 𝓕τ_h - τ_h = d dx on Schwartz tests (S3.1). -/
theorem square_fourier_defect (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) :
    (∀ φ : 𝓢(ℝ, ℂ), tsupport φ ⊆ Ioo (-1) 1 → squareGapMeasure h A φ = 0) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∀ x, 0 ≤ (φ x).re ∧ (φ x).im = 0) → (∀ n : ℤ, φ n = 0) →
      0 ≤ (squareGapMeasure h A φ).re) ∧
    (∃ M : ℝ, ∀ x, ‖A - h x‖ ^ 2 ≤ M) ∧
    Continuous (squareDualityDefect h) ∧ Tendsto (squareDualityDefect h) (cocompact ℝ) (𝓝 0) ∧
    (∀ x, (squareDualityDefect h x).im = 0) ∧
    (∀ x, squareDualityDefect h x = 𝓕 (fun y => h y * conj (h y)) x - h x * conj (h x)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), squareGapMeasure h A (𝓕 φ) - squareGapMeasure h A φ = ∫ x, squareDualityDefect h x * φ x) := by
  refine ⟨fun φ hφ => squareGapMeasure_gap hpl φ hφ, fun φ hφ hZ => ?_, ?_,
    continuous_squareDualityDefect hcont hint hL2 hsd hev, tendsto_squareDualityDefect hint hsd hev hvan,
    squareDualityDefect_im, fun x => by rw [squareDualityDefect, autocorr_eq_fourier hint hsd hev],
    squareGapMeasure_fourier_defect hint hL2 hsd hev A⟩
  · have hs : (∑' n : ℤ, (if n = 0 then 0 else φ n)) = 0 :=
      (tsum_congr fun n => by split_ifs <;> simp [hZ]).trans tsum_zero
    have hI : Integrable (fun x => ((‖A - h x‖ ^ 2 : ℝ) : ℂ) * φ x) := by
      obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖h x‖ ≤ M := by
        obtain ⟨K, hK, hKs⟩ : ∃ K : Set ℝ, IsCompact K ∧ ∀ x ∉ K, ‖h x‖ < 1 := by
          have := hvan (Metric.ball_mem_nhds 0 one_pos)
          rw [Filter.mem_map, Filter.mem_cocompact] at this
          obtain ⟨K, hK, hKs⟩ := this
          exact ⟨K, hK, fun x hx => by simpa using hKs hx⟩
        obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
        exact ⟨max B 1, fun x => by
          by_cases hx : x ∈ K
          · exact (hB x hx).trans (le_max_left _ _)
          · exact (hKs x hx).le.trans (le_max_right _ _)⟩
      refine φ.integrable.bdd_mul (c := (‖A‖ + M) ^ 2) (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hM x])) 2
    rw [squareGapMeasure, hs, mul_zero, sub_zero]
    have hre := integral_re hI
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine integral_nonneg fun x => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (sq_nonneg _) (hφ x).1
  · obtain ⟨K, hK, hKs⟩ : ∃ K : Set ℝ, IsCompact K ∧ ∀ x ∉ K, ‖h x‖ < 1 := by
      have := hvan (Metric.ball_mem_nhds 0 one_pos)
      rw [Filter.mem_map, Filter.mem_cocompact] at this
      obtain ⟨K, hK, hKs⟩ := this
      exact ⟨K, hK, fun x hx => by simpa using hKs hx⟩
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨(‖A‖ + max B 1) ^ 2, fun x => ?_⟩
    have hx : ‖h x‖ ≤ max B 1 := by
      by_cases hxK : x ∈ K
      · exact (hB x hxK).trans (le_max_left _ _)
      · exact (hKs x hxK).le.trans (le_max_right _ _)
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) 2

/-- R2-S3 (S3.2): the C₀ defect at the origin is d(0) = ‖h‖₂² - |A|² > 0 for nonzero h (with
complex conjugation retained): ≥ |A|² when A ≠ 0 (h = A on an interval of length two) and > 0
when A = 0. -/
theorem square_defect_origin_positive (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hL2 : MemLp h 2) (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    squareDualityDefect h 0 = (((∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 : ℝ) : ℂ) ∧
    0 < (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 ∧
    (A ≠ 0 → ‖A‖ ^ 2 ≤ (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2) ∧
    (A = 0 → 0 < ∫ x, ‖h x‖ ^ 2) := by
  obtain ⟨hgt, hge⟩ := norm_sq_gt hcont hL2 hpl hne
  refine ⟨squareDualityDefect_zero hev hpl, by linarith, fun _ => by linarith, fun hA => ?_⟩
  subst hA; simpa using hgt

/-- R2-S3: no tempered lattice-supported order-zero correction σ = Σ c_n δ_n makes τ_h + σ
self-dual: the transform of σ is 1-periodic, so the continuous C₀ defect would be 1-periodic,
hence zero, contradicting d(0) > 0. -/
theorem square_no_lattice_repair (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    ¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧ ∀ φ : 𝓢(ℝ, ℂ),
      squareGapMeasure h A (𝓕 φ) + latticePairing c (𝓕 φ) = squareGapMeasure h A φ + latticePairing c φ := by
  refine no_lattice_repair hcont hint hL2 hsd hev hvan A ?_
  obtain ⟨h0, hpos, -⟩ := square_defect_origin_positive hev hcont hL2 hpl hne
  rw [h0]; exact_mod_cast hpos.ne'

/-- R2-S3 (S3.3): the self-dual projection τ⁺ = (τ_h + 𝓕τ_h)/2 (the parent
`involutionSelfdualProjection`) is self-dual and equals τ_h + d/2 dx, so on a nonempty interval
(-ε, ε) inside the old gap its density d/2 is strictly positive. -/
theorem square_selfdual_projection_fills_gap (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    fourierFunctional (Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A)) =
      Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) ∧
    (∀ φ : 𝓢(ℝ, ℂ), Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
      squareGapMeasure h A φ + (1 / 2) * ∫ x, squareDualityDefect h x * φ x) ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (∀ x ∈ Ioo (-ε) ε, 0 < (squareDualityDefect h x).re ∧ (squareDualityDefect h x).im = 0) ∧
      ∀ φ : 𝓢(ℝ, ℂ), tsupport φ ⊆ Ioo (-ε) ε →
        Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
          ∫ x, (squareDualityDefect h x / 2) * φ x := by
  have hS := squareGapMeasure_fourier_defect hint hL2 hsd hev A
  have hproj : ∀ φ : 𝓢(ℝ, ℂ), Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
      squareGapMeasure h A φ + (1 / 2) * ∫ x, squareDualityDefect h x * φ x := by
    intro φ
    simp only [Zeta23.OPICA.involutionSelfdualProjection, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      fourierFunctional, LinearMap.coe_mk, AddHom.coe_mk]
    have := hS φ
    linear_combination (1 / 2 : ℂ) * this
  refine ⟨?_, hproj, ?_⟩
  · funext φ
    simp only [Zeta23.OPICA.involutionSelfdualProjection, fourierFunctional, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.smul_apply, Pi.add_apply, smul_eq_mul, fourier_fourier_schwartz,
      squareGapMeasure_reflect hev]
    ring
  · obtain ⟨h0, hpos, -⟩ := square_defect_origin_positive hev hcont hL2 hpl hne
    have hdc := continuous_squareDualityDefect hcont hint hL2 hsd hev
    set c0 : ℝ := (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hdc 0 (c0 / 2) (by positivity)
    refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num),
      fun x hx => ?_, fun φ hφ => ?_⟩
    · have hd : dist x 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith [hx.1, hx.2, min_le_left δ (1 / 2)]
      have := hball x hd
      rw [h0, Complex.dist_eq] at this
      refine ⟨?_, squareDualityDefect_im x⟩
      have hre := (Complex.abs_re_le_norm (squareDualityDefect h x - (c0 : ℂ))).trans_lt this
      rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at hre
      linarith [hre.1]
    · have hφ1 : tsupport φ ⊆ Ioo (-1) 1 := hφ.trans (Ioo_subset_Ioo
        (by linarith [min_le_right δ (1 / 2)]) (by linarith [min_le_right δ (1 / 2)]))
      rw [hproj, squareGapMeasure_gap hpl φ hφ1, zero_add, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

end Roots

end Zeta23.OPICAFollowup
