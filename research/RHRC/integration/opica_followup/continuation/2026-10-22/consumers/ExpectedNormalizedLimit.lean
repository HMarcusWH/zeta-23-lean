import Zeta23.OPICAFollowup.NearGapLimits

/- Independent consumers for the original R1-CT1 root
`Zeta23.OPICAFollowup.dilation_normalized_limit_not_measure`.

The limit is restated existentially and pinned down pointwise by its explicit
lattice formula, so no source definition can hide a different object. The
domain consumer uses the paper's explicit three-comb pairing
D_L + D_(-L) - 2cosh(L/2) D_0 on 0 < L < log 2. Boundary consumers check the
cancelled origin coefficient, the coefficient 2n² of a quadratic bump at every
integer, and the failure of any common normalized variation constant. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICANormalizedLimitIndependent

/-- Explicit lattice value Σ_n (n² φ''(n) + 2n φ'(n)). -/
def latticeValue (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∑' n : ℤ, ((n : ℂ) ^ 2 * deriv (deriv φ) n + 2 * n * deriv φ n)

/-- Complete semantic restatement: a tempered distribution exists that is the
𝓢'-limit of ν_L/L², equals the explicit lattice value on every test, is the
pointwise sum of n² δ_n'' − 2n δ_n', is nonzero, is not of order zero at any
nonzero integer and is not given by a locally finite Jordan pair. -/
theorem expected_dilation_normalized_limit_not_measure :
    ∃ T : TemperedDistribution ℝ ℂ,
      Tendsto (fun L : ℝ => ((L : ℂ) ^ 2)⁻¹ •
          (nearGapCombFamily L).distributionOfLinearGrowth (nearGapCombFamily_growth L))
        (𝓝[≠] 0) (𝓝 T) ∧
      (∀ φ : SchwartzMap ℝ ℂ, T φ = latticeValue φ) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        HasSum (fun n : ℤ => ((n : ℂ) ^ 2 • TemperedDistribution.derivCLM ℂ
            (TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta (n : ℝ))) -
          (2 * (n : ℂ)) • TemperedDistribution.derivCLM ℂ
            (TemperedDistribution.delta (n : ℝ))) φ) (T φ)) ∧
      T ≠ 0 ∧
      (∀ n : ℤ, n ≠ 0 → ¬ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ,
        tsupport φ ⊆ Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) →
          ‖T φ‖ ≤ C * SchwartzMap.seminorm ℝ 0 0 φ) ∧
      (¬ ∃ μ : LocallyFiniteSignedMeasure, ∀ φ : SchwartzMap ℝ ℂ,
        (∫ x, φ x ∂μ.positive) - (∫ x, φ x ∂μ.negative) = T φ) := by
  obtain ⟨h1, -, h3, -, h5, h6, h7, -⟩ := dilation_normalized_limit_not_measure
  exact ⟨ct1NormalizedLimit, h1, ct1NormalizedLimit_apply, h3, h5, h6, h7⟩

/-- The paper's domain 0 < L < log 2 as L → 0⁺, on the explicit three-comb
pairing e^{L/2}Σφ(e^L n) + e^{-L/2}Σφ(e^{-L} n) − 2cosh(L/2)Σφ(n). -/
theorem expected_three_comb_normalized_limit (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun L : ℝ =>
        ((Real.exp (L / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp L * n) +
          (Real.exp (-L / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp (-L) * n) -
          ((2 * Real.cosh (L / 2) : ℝ) : ℂ) * ∑' n : ℤ, φ n) / (L : ℂ) ^ 2)
      (𝓝[>] 0) (𝓝 (latticeValue φ)) := by
  have h := (dilation_normalized_limit_not_measure.2.1 φ).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun x hx => ne_of_gt hx))
  refine h.congr (fun L => ?_)
  congr 1
  rw [nearGapCombDistribution_eq_explicit]
  change dilatedCombDistribution L φ + dilatedCombDistribution (-L) φ -
    ((2 * Real.cosh (L / 2) : ℝ) : ℂ) • dilatedCombDistribution 0 φ = _
  rw [dilatedCombDistribution_apply, dilatedCombDistribution_apply,
    dilatedCombDistribution_apply, smul_eq_mul]
  simp only [Real.exp_zero, zero_div, Complex.ofReal_one, one_mul, neg_div]

/-- The cancelled origin coefficient: tests near 0 see nothing. -/
theorem expected_origin_coefficient_zero (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport φ ⊆ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    ct1NormalizedLimit φ = 0 := by
  have h := dilation_normalized_limit_not_measure.2.2.2.1 0 φ (by simpa using hφ)
  simpa using h

/-- Every integer n carries the nonzero second-derivative coefficient n²:
a quadratic bump at n has limit value 2n². -/
theorem expected_integer_coefficients (n : ℤ) (hn : n ≠ 0) :
    ∃ φ : SchwartzMap ℝ ℂ, tsupport φ ⊆ Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) ∧
      ct1NormalizedLimit φ = 2 * (n : ℂ) ^ 2 ∧ ct1NormalizedLimit φ ≠ 0 := by
  refine ⟨ct1BumpTest n (ε := 1 / 4) (by norm_num),
    ct1BumpTest_tsupport_Icc n (by norm_num) (by norm_num),
    ct1NormalizedLimit_bumpTest n (by norm_num) (by norm_num), ?_⟩
  rw [ct1NormalizedLimit_bumpTest n (by norm_num) (by norm_num)]
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 this)

/-- No common constant bounds the normalized variation near 1 on the CT1
domain: the HT2 common-growth premise genuinely fails after normalization. -/
theorem expected_no_common_normalized_variation :
    ¬ ∃ C : ℝ, ∀ L : ℝ, 0 < L → L < Real.log 2 →
      (nearGapCombFamily L).totalVariation.real (Icc (1 / 2) (3 / 2)) / L ^ 2 ≤ C := by
  rintro ⟨C, hC⟩
  have hT := dilation_normalized_limit_not_measure.2.2.2.2.2.2.2
  have hev := hT.eventually (eventually_gt_atTop C)
  have hdom : ∀ᶠ L in 𝓝[>] (0 : ℝ), L ∈ Ioo 0 (Real.log 2) :=
    Ioo_mem_nhdsGT (Real.log_pos (by norm_num))
  obtain ⟨L, hL1, hL2⟩ := (hev.and hdom).exists
  linarith [hC L hL2.1 hL2.2]

/-- Self-duality of the limit, restated with the canonical Fourier transform
evaluated on tests: T(𝓕φ) = T(φ). -/
theorem expected_normalized_limit_selfdual (φ : SchwartzMap ℝ ℂ) :
    ct1NormalizedLimit (𝓕 φ) = ct1NormalizedLimit φ := by
  have h := ct1NormalizedLimit_fourier_selfdual
  calc ct1NormalizedLimit (𝓕 φ) = (𝓕 ct1NormalizedLimit) φ := rfl
    _ = ct1NormalizedLimit φ := by rw [h]

end OPICANormalizedLimitIndependent
#print axioms Zeta23.OPICAFollowup.dilation_normalized_limit_not_measure
#print axioms Zeta23.OPICAFollowup.ct1NormalizedLimit_apply
#print axioms OPICANormalizedLimitIndependent.expected_dilation_normalized_limit_not_measure
#print axioms OPICANormalizedLimitIndependent.expected_three_comb_normalized_limit
#print axioms OPICANormalizedLimitIndependent.expected_origin_coefficient_zero
#print axioms OPICANormalizedLimitIndependent.expected_integer_coefficients
#print axioms OPICANormalizedLimitIndependent.expected_no_common_normalized_variation
#print axioms Zeta23.OPICAFollowup.ct1NormalizedLimit_fourier_selfdual
#print axioms OPICANormalizedLimitIndependent.expected_normalized_limit_selfdual
