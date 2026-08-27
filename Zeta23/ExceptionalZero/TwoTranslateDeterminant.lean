import Zeta23.ExceptionalZero.TwoTranslateNegativity
import Zeta23.ExceptionalZero.ArithmeticReduction

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

/-!
# X4: two-translate determinant RH-equivalence audit

X3 proves that every hypothetical off-critical zeta zero produces a real-even C² compactly
supported test and aperture for which the complete two-translate Weil correlation strictly
dominates the fixed diagonal.  X4 classifies the corresponding universal determinant inequality
before any arithmetic-side rewrite is attempted.

The scalar below is deliberately real:
  Δ_f(t) = ‖W(f,f)‖² - ‖W(T_t f,f)‖².
Because the diagonal Weil value is real, this is exactly the determinant of the Hermitian
two-translate matrix after coercion to ℂ.

The endpoint of this file is an equivalence between universal nonnegativity of this determinant
gap on the real-even C² compact-support test class and the repository's critical-line statement.
This is an RH-equivalence audit, not a proof of RH and not an unconditional positivity theorem.
-/

/-- Real determinant gap of the complete two-translate Weil matrix. -/
def twoTranslateDeterminantGap
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖Z.W f f‖ ^ 2 - ‖weilRelativeCorrelation Z f t‖ ^ 2

/-- The real gap is exactly the complex determinant of the live Hermitian two-translate matrix. -/
theorem twoTranslateWeilMatrix_det_eq_gap
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) :
    Matrix.det (twoTranslateWeilMatrix Z f t) =
      ((twoTranslateDeterminantGap Z f t : ℝ) : ℂ) := by
  have hdiag :
      Z.W f f * Z.W f f = (‖Z.W f f‖ : ℂ) ^ 2 := by
    calc
      Z.W f f * Z.W f f =
          (starRingEnd ℂ) (Z.W f f) * Z.W f f := by
            rw [W_self_star]
      _ = (‖Z.W f f‖ : ℂ) ^ 2 := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
        push_cast
        ring
  have hcorr :
      (starRingEnd ℂ) (weilRelativeCorrelation Z f t) *
          weilRelativeCorrelation Z f t =
        (‖weilRelativeCorrelation Z f t‖ : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [Matrix.det_fin_two]
  simp [twoTranslateWeilMatrix]
  rw [hdiag, hcorr]
  unfold twoTranslateDeterminantGap
  push_cast
  ring

/-- X3's strict correlation-over-diagonal inequality is exactly a negative determinant gap. -/
theorem twoTranslateDeterminantGap_neg_of_diagonal_norm_lt
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ)
    (hgt : ‖Z.W f f‖ < ‖weilRelativeCorrelation Z f t‖) :
    twoTranslateDeterminantGap Z f t < 0 := by
  unfold twoTranslateDeterminantGap
  have hd : 0 ≤ ‖Z.W f f‖ := norm_nonneg _
  have hc : 0 ≤ ‖weilRelativeCorrelation Z f t‖ := norm_nonneg _
  nlinarith

/-- X3 restated at the determinant frontier: every off-critical zero produces an admissible
real-even test and nonnegative aperture with strictly negative complete two-translate determinant. -/
theorem exists_realEven_twoTranslate_negativeDeterminant_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier) (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ k : ℝ → ℂ, ∃ a : ℝ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ Function.Even k ∧
        (∀ x : ℝ, (k x).im = 0) ∧
        paperFT k (I / 2) = 0 ∧ paperFT k (-I / 2) = 0 ∧
        0 ≤ a ∧
        twoTranslateDeterminantGap zetaZeroConfig k (2 * a) < 0 := by
  obtain ⟨k, a, hk, hkc, heven, hreal, hp, hn, ha, hgt, _hneg⟩ :=
    exists_realEven_poleKilled_twoTranslate_negativeWitness_of_offLine_zero ρ₀ hoff
  exact ⟨k, a, hk, hkc, heven, hreal, hp, hn, ha,
    twoTranslateDeterminantGap_neg_of_diagonal_norm_lt
      zetaZeroConfig k (2 * a) hgt⟩

/-- Universal X4 determinant property on the natural real-even C² compact-support class.
Pole-neutrality is intentionally not part of the property: it is construction-specific to X3,
whereas the determinant statement itself does not depend on how a test was produced. -/
def UniversalRealEvenTwoTranslateDeterminantNonnegative : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Function.Even k → (∀ x : ℝ, (k x).im = 0) →
    ∀ a : ℝ, 0 ≤ twoTranslateDeterminantGap zetaZeroConfig k (2 * a)

/-- Universal nonnegativity excludes every off-critical zero by the X3 adaptive witness. -/
theorem criticalLine_of_universalRealEvenTwoTranslateDeterminantNonnegative
    (hdet : UniversalRealEvenTwoTranslateDeterminantNonnegative) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hoff
  obtain ⟨k, a, hk, hkc, heven, hreal, _hp, _hn, _ha, hneg⟩ :=
    exists_realEven_twoTranslate_negativeDeterminant_of_offLine_zero
      ⟨ρ, hρ⟩ hoff
  have hnonneg := hdet k hk hkc heven hreal a
  exact (not_lt_of_ge hnonneg) hneg

/-- On the critical line, the centered spectral coordinate is real. -/
theorem gammaOf_star_eq_self_of_criticalLine
    (ρ : zetaZeroConfig.carrier)
    (hline : (ρ : ℂ).re = 1 / 2) :
    (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (ρ : ℂ) := by
  have him : (gammaOf (ρ : ℂ)).im = 0 := by
    rw [Zeta23.WeilEF.gammaOf_im, hline]
    norm_num
  apply Complex.ext
  · simp
  · simp [him]

/-- For a real-even test, the Fourier value at a critical-line spectral coordinate is real. -/
theorem paperFT_im_eq_zero_at_criticalLine_of_real_even
    {k : ℝ → ℂ} (hreal : ∀ x : ℝ, (k x).im = 0)
    (heven : Function.Even k) (ρ : zetaZeroConfig.carrier)
    (hline : (ρ : ℂ).re = 1 / 2) :
    (paperFT k (gammaOf (ρ : ℂ))).im = 0 := by
  have hstar :=
    star_paperFT_star_eq_paperFT_of_real_even
      hreal heven (gammaOf (ρ : ℂ))
  rw [gammaOf_star_eq_self_of_criticalLine ρ hline] at hstar
  have him := congrArg Complex.im hstar
  simp only [Complex.conj_im] at him
  linarith

/-- Under the critical-line hypothesis, every multiplicity-weighted squared-filter coefficient is
a nonnegative real number. -/
theorem squaredWeilZeroFilter_coeff_re_nonneg_of_criticalLine
    {k : ℝ → ℂ} (hreal : ∀ x : ℝ, (k x).im = 0)
    (heven : Function.Even k) (ρ : zetaZeroConfig.carrier)
    (hline : (ρ : ℂ).re = 1 / 2) :
    0 ≤ (zeroFilterCoeff (squaredWeilZeroFilter k) ρ).re := by
  have him :=
    paperFT_im_eq_zero_at_criticalLine_of_real_even hreal heven ρ hline
  rw [zeroFilterCoeff_squaredWeilZeroFilter]
  simp [pow_two, Complex.mul_re, him]
  positivity

/-- The same critical-line coefficient has zero imaginary part. -/
theorem squaredWeilZeroFilter_coeff_im_eq_zero_of_criticalLine
    {k : ℝ → ℂ} (hreal : ∀ x : ℝ, (k x).im = 0)
    (heven : Function.Even k) (ρ : zetaZeroConfig.carrier)
    (hline : (ρ : ℂ).re = 1 / 2) :
    (zeroFilterCoeff (squaredWeilZeroFilter k) ρ).im = 0 := by
  have him :=
    paperFT_im_eq_zero_at_criticalLine_of_real_even hreal heven ρ hline
  rw [zeroFilterCoeff_squaredWeilZeroFilter]
  simp [pow_two, Complex.mul_im, him]

/-- Hence coefficient norm equals coefficient real part on the critical line. -/
theorem norm_squaredWeilZeroFilter_coeff_eq_re_of_criticalLine
    {k : ℝ → ℂ} (hreal : ∀ x : ℝ, (k x).im = 0)
    (heven : Function.Even k) (ρ : zetaZeroConfig.carrier)
    (hline : (ρ : ℂ).re = 1 / 2) :
    ‖zeroFilterCoeff (squaredWeilZeroFilter k) ρ‖ =
      (zeroFilterCoeff (squaredWeilZeroFilter k) ρ).re := by
  have hre :=
    squaredWeilZeroFilter_coeff_re_nonneg_of_criticalLine
      hreal heven ρ hline
  have him :=
    squaredWeilZeroFilter_coeff_im_eq_zero_of_criticalLine
      hreal heven ρ hline
  have hz :
      zeroFilterCoeff (squaredWeilZeroFilter k) ρ =
        (((zeroFilterCoeff (squaredWeilZeroFilter k) ρ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  rw [hz]
  simp [Real.norm_eq_abs, abs_of_nonneg hre]

/-- At aperture zero the squared-filter coefficient mass is exactly the real diagonal Weil value. -/
theorem squaredWeilZeroFilter_coeffMass_eq_W_re_of_criticalLine
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hreal : ∀ x : ℝ, (k x).im = 0) (heven : Function.Even k)
    (hline : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2) :
    (∑' ρ : zetaZeroConfig.carrier,
        ‖zeroFilterCoeff (squaredWeilZeroFilter k) ρ‖) =
      (zetaZeroConfig.W k k).re := by
  have hφ := absolutelySummableZeroFilter_squaredWeil hk hkc
  have hsum :
      Summable (fun ρ : zetaZeroConfig.carrier =>
        zeroFilterCoeff (squaredWeilZeroFilter k) ρ) :=
    summable_norm_iff.mp hφ
  have hzero :=
    weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared
      hreal heven 0
  have hself :
      zetaZeroConfig.W k k =
        ∑' ρ : zetaZeroConfig.carrier,
          zeroFilterCoeff (squaredWeilZeroFilter k) ρ := by
    simpa [weilRelativeCorrelation, translateRight,
      filteredZeroFamily, filteredZeroTerm] using hzero
  rw [hself, Complex.re_tsum hsum]
  exact tsum_congr (fun ρ =>
    norm_squaredWeilZeroFilter_coeff_eq_re_of_criticalLine
      hreal heven ρ (hline ρ))

/-- RH bounds every real-even complete two-translate correlation by its fixed diagonal norm. -/
theorem norm_weilRelativeCorrelation_le_diagonal_of_criticalLine
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hreal : ∀ x : ℝ, (k x).im = 0) (heven : Function.Even k)
    (hline : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2)
    (a : ℝ) :
    ‖weilRelativeCorrelation zetaZeroConfig k (2 * a)‖ ≤
      ‖zetaZeroConfig.W k k‖ := by
  have hφ := absolutelySummableZeroFilter_squaredWeil hk hkc
  have hc : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hbound :=
    norm_filteredZeroFamily_le_coeffMass_of_criticalLine
      hφ hc hline a
  rw [← weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared hreal heven a] at hbound
  rw [squaredWeilZeroFilter_coeffMass_eq_W_re_of_criticalLine
      hk hkc hreal heven hline] at hbound
  exact hbound.trans (Complex.re_le_norm _)

/-- Critical-line placement therefore implies universal nonnegativity of the X4 determinant gap. -/
theorem universalRealEvenTwoTranslateDeterminantNonnegative_of_criticalLine
    (hRH : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) :
    UniversalRealEvenTwoTranslateDeterminantNonnegative := by
  intro k hk hkc heven hreal a
  have hline : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => hRH (ρ : ℂ) ρ.2
  have hle :=
    norm_weilRelativeCorrelation_le_diagonal_of_criticalLine
      hk hkc hreal heven hline a
  unfold twoTranslateDeterminantGap
  have hd : 0 ≤ ‖zetaZeroConfig.W k k‖ := norm_nonneg _
  have hc : 0 ≤ ‖weilRelativeCorrelation zetaZeroConfig k (2 * a)‖ := norm_nonneg _
  nlinarith

/-- **X4 moustache audit.**  Universal nonnegativity of the complete real-even two-translate
determinant gap is exactly equivalent to the critical-line statement.  It is therefore an
RH-equivalent frontier, not an independent weaker positivity target. -/
theorem universalRealEvenTwoTranslateDeterminantNonnegative_iff_criticalLine :
    UniversalRealEvenTwoTranslateDeterminantNonnegative ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 :=
  ⟨criticalLine_of_universalRealEvenTwoTranslateDeterminantNonnegative,
    universalRealEvenTwoTranslateDeterminantNonnegative_of_criticalLine⟩

#print axioms Zeta23.ExceptionalZero.twoTranslateWeilMatrix_det_eq_gap
#print axioms Zeta23.ExceptionalZero.exists_realEven_twoTranslate_negativeDeterminant_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.criticalLine_of_universalRealEvenTwoTranslateDeterminantNonnegative
#print axioms Zeta23.ExceptionalZero.universalRealEvenTwoTranslateDeterminantNonnegative_of_criticalLine
#print axioms Zeta23.ExceptionalZero.universalRealEvenTwoTranslateDeterminantNonnegative_iff_criticalLine

end Zeta23.ExceptionalZero
