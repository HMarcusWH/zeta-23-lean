import Zeta23.ExceptionalZero.TwoTranslateSpectrum
import Zeta23.ExceptionalZero.TwoTranslateCorrelation
import Zeta23.ExceptionalZero.TwoTranslateVisibility
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

/-!
# X3: off-line zeros force a negative complete two-translate Weil object

X0 fixed the exact Hermitian two-translate matrix. X1 supplies target-adaptive real-even
pole-neutral tests. X2 identifies the genuine relative correlation with the generic R001
filtered-zero family of the squared Weil filter.

X3 composes those green interfaces. A hypothetical off-critical zero is reflected to the
right half-strip when necessary, R001 forces the complete correlation to escape every
subexponential bound, and an explicit division-free phase witness turns a sufficiently large
correlation into a strict negative Hermitian quadratic value.

No positivity theorem, determinant inequality, RH implication, or RH-equivalence claim is made
here. The conclusion is the M2 obstruction direction only: an off-line zero forces a complete
adaptive two-translate Weil matrix which is not positive semidefinite.
-/

/-- Division-free phase-aligned witness for the Hermitian matrix with diagonal d and off-diagonal
entries star C and C. -/
def twoTranslatePhaseWitness (C : ℂ) : Fin 2 → ℂ :=
  ![(‖C‖ : ℂ), -C]

/-- Exact quadratic value of the phase witness. No assumption on the diagonal is needed for the
algebraic identity. -/
theorem twoTranslatePhaseWitness_value
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) :
    star (twoTranslatePhaseWitness (weilRelativeCorrelation Z f t)) ⬝ᵥ
        (twoTranslateWeilMatrix Z f t *ᵥ
          twoTranslatePhaseWitness (weilRelativeCorrelation Z f t)) =
      ((2 * ‖weilRelativeCorrelation Z f t‖ ^ 2 : ℝ) : ℂ) *
        (Z.W f f - (‖weilRelativeCorrelation Z f t‖ : ℂ)) := by
  simp [twoTranslatePhaseWitness, twoTranslateWeilMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- If the complete relative correlation strictly dominates the norm of the fixed diagonal, the
explicit phase witness has a strictly negative real quadratic value. -/
theorem twoTranslatePhaseWitness_neg_of_diagonal_norm_lt
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ)
    (hgt : ‖Z.W f f‖ < ‖weilRelativeCorrelation Z f t‖) :
    (star (twoTranslatePhaseWitness (weilRelativeCorrelation Z f t)) ⬝ᵥ
        (twoTranslateWeilMatrix Z f t *ᵥ
          twoTranslatePhaseWitness (weilRelativeCorrelation Z f t))).re < 0 := by
  rw [twoTranslatePhaseWitness_value]
  have hr : 0 < ‖weilRelativeCorrelation Z f t‖ :=
    lt_of_le_of_lt (norm_nonneg _) hgt
  have hdre : (Z.W f f).re < ‖weilRelativeCorrelation Z f t‖ := by
    exact lt_of_le_of_lt
      (le_trans (le_abs_self (Z.W f f).re) (Complex.abs_re_le_norm (Z.W f f))) hgt
  have hcoef : 0 < 2 * ‖weilRelativeCorrelation Z f t‖ ^ 2 := by positivity
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg hcoef (sub_neg.mpr hdre)

/-- A strict correlation-over-diagonal witness rules out positive semidefiniteness of the complete
Hermitian two-translate Weil matrix. -/
theorem twoTranslateWeilMatrix_not_posSemidef_of_diagonal_norm_lt
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ)
    (hgt : ‖Z.W f f‖ < ‖weilRelativeCorrelation Z f t‖) :
    ¬ (twoTranslateWeilMatrix Z f t).PosSemidef := by
  intro hpsd
  have hnonneg :=
    hpsd.re_dotProduct_nonneg
      (twoTranslatePhaseWitness (weilRelativeCorrelation Z f t))
  have hneg := twoTranslatePhaseWitness_neg_of_diagonal_norm_lt Z f t hgt
  exact (not_lt_of_ge hnonneg) hneg

/-- Elementary growth extraction. If a real profile is not subexponential, then it exceeds every
fixed threshold at some nonnegative aperture. -/
theorem exists_nonneg_gt_of_not_subexponential
    {R : ScaleProfile} (hnot : ¬ Subexponential R) (M : ℝ) :
    ∃ a : ℝ, 0 ≤ a ∧ M < R a := by
  by_contra hex
  have hbound : ∀ a : ℝ, 0 ≤ a → R a ≤ M := by
    intro a ha
    by_contra hle
    have hgt : M < R a := lt_of_not_ge hle
    exact hex ⟨a, ha, hgt⟩
  apply hnot
  intro ε hε
  let A : ℝ := max 0 ((M - 1) / ε)
  refine ⟨A, ?_⟩
  intro a ha
  have hA0 : 0 ≤ A := le_max_left _ _
  have ha0 : 0 ≤ a := hA0.trans ha
  have hfrac : M - 1 ≤ A * ε := by
    exact (div_le_iff₀ hε).mp (le_max_right 0 ((M - 1) / ε))
  have hM : M ≤ 1 + ε * a := by
    nlinarith
  calc
    R a ≤ M := hbound a ha0
    _ ≤ 1 + ε * a := hM
    _ ≤ Real.exp (ε * a) := Real.add_one_le_exp (ε * a)

/-- X2 plus generic R001 handoff: a visible right-half zero makes the genuine complete relative
correlation non-subexponential. -/
theorem not_subexponential_weilRelativeCorrelation_of_right_zero
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hreal : ∀ x : ℝ, (k x).im = 0) (heven : Function.Even k)
    (ρ₀ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ₀ : ℂ).re)
    (hvis : paperFT k (gammaOf (ρ₀ : ℂ)) ≠ 0) :
    ¬ Subexponential
      (fun a => ‖weilRelativeCorrelation zetaZeroConfig k (2 * a)‖) := by
  have hφ := absolutelySummableZeroFilter_squaredWeil hk hkc
  have hc : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hcoeff : zeroFilterCoeff (squaredWeilZeroFilter k) ρ₀ ≠ 0 := by
    rw [zeroFilterCoeff_squaredWeilZeroFilter]
    refine mul_ne_zero ?_ (pow_ne_zero 2 hvis)
    have hmNat : 1 ≤ zeroMult (ρ₀ : ℂ) :=
      zetaZeroConfig.one_le_mult (ρ₀ : ℂ) ρ₀.2
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hmNat
  have hR001 :=
    not_subexponential_filteredZeroFamily_of_right_zero hφ hc ρ₀ hright hcoeff
  intro hsub
  apply hR001
  intro ε hε
  obtain ⟨A, hA⟩ := hsub ε hε
  refine ⟨A, fun a ha => ?_⟩
  rw [← weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared hreal heven a]
  exact hA a ha

/-- Reflection provenance for an arbitrary off-critical zeta zero. The returned right-half zero is
either the input itself or its canonical reflected partner. -/
theorem exists_rightHalf_reflection_of_offLine
    (ρ₀ : zetaZeroConfig.carrier) (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ ρR : zetaZeroConfig.carrier,
      (ρR = ρ₀ ∨ ρR = zetaZeroConfig.reflectEquiv ρ₀) ∧
        1 / 2 < (ρR : ℂ).re := by
  by_cases hright : 1 / 2 < (ρ₀ : ℂ).re
  · exact ⟨ρ₀, Or.inl rfl, hright⟩
  · have hle : (ρ₀ : ℂ).re ≤ 1 / 2 := le_of_not_gt hright
    have hleft : (ρ₀ : ℂ).re < 1 / 2 := lt_of_le_of_ne hle hoff
    refine ⟨zetaZeroConfig.reflectEquiv ρ₀, Or.inr rfl, ?_⟩
    change 1 / 2 < (reflect (ρ₀ : ℂ)).re
    simp [reflect]
    linarith

/-- Right-half X3 endpoint with the actual negative witness exposed. -/
theorem exists_realEven_poleKilled_twoTranslate_negativeWitness_of_right_zero
    (ρ₀ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ₀ : ℂ).re) :
    ∃ k : ℝ → ℂ, ∃ a : ℝ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ Function.Even k ∧
        (∀ x : ℝ, (k x).im = 0) ∧
        paperFT k (I / 2) = 0 ∧ paperFT k (-I / 2) = 0 ∧
        0 ≤ a ∧
        ‖zetaZeroConfig.W k k‖ <
          ‖weilRelativeCorrelation zetaZeroConfig k (2 * a)‖ ∧
        (star (twoTranslatePhaseWitness
            (weilRelativeCorrelation zetaZeroConfig k (2 * a))) ⬝ᵥ
          (twoTranslateWeilMatrix zetaZeroConfig k (2 * a) *ᵥ
            twoTranslatePhaseWitness
              (weilRelativeCorrelation zetaZeroConfig k (2 * a)))).re < 0 := by
  obtain ⟨k, hk, hkc, heven, hreal, hp, hn, hvis⟩ :=
    exists_realEven_poleKilled_visible_test ρ₀
  have hnot :=
    not_subexponential_weilRelativeCorrelation_of_right_zero
      hk hkc hreal heven ρ₀ hright hvis
  obtain ⟨a, ha, hgt⟩ :=
    exists_nonneg_gt_of_not_subexponential hnot ‖zetaZeroConfig.W k k‖
  have hneg :=
    twoTranslatePhaseWitness_neg_of_diagonal_norm_lt
      zetaZeroConfig k (2 * a) hgt
  exact ⟨k, a, hk, hkc, heven, hreal, hp, hn, ha, hgt, hneg⟩

/-- X3 / M2 endpoint. Any hypothetical off-critical zeta zero forces an admissible real-even
pole-neutral test and a nonnegative relative aperture whose complete Hermitian two-translate Weil
matrix has a strict negative direction. -/
theorem exists_realEven_poleKilled_twoTranslate_negativeWitness_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier) (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ k : ℝ → ℂ, ∃ a : ℝ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ Function.Even k ∧
        (∀ x : ℝ, (k x).im = 0) ∧
        paperFT k (I / 2) = 0 ∧ paperFT k (-I / 2) = 0 ∧
        0 ≤ a ∧
        ‖zetaZeroConfig.W k k‖ <
          ‖weilRelativeCorrelation zetaZeroConfig k (2 * a)‖ ∧
        (star (twoTranslatePhaseWitness
            (weilRelativeCorrelation zetaZeroConfig k (2 * a))) ⬝ᵥ
          (twoTranslateWeilMatrix zetaZeroConfig k (2 * a) *ᵥ
            twoTranslatePhaseWitness
              (weilRelativeCorrelation zetaZeroConfig k (2 * a)))).re < 0 := by
  obtain ⟨ρR, _hprov, hright⟩ :=
    exists_rightHalf_reflection_of_offLine ρ₀ hoff
  exact exists_realEven_poleKilled_twoTranslate_negativeWitness_of_right_zero ρR hright

/-- Non-PSD corollary of the explicit X3 witness. -/
theorem exists_realEven_poleKilled_twoTranslate_not_posSemidef_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier) (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ k : ℝ → ℂ, ∃ a : ℝ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ Function.Even k ∧
        (∀ x : ℝ, (k x).im = 0) ∧
        paperFT k (I / 2) = 0 ∧ paperFT k (-I / 2) = 0 ∧
        0 ≤ a ∧
        ¬ (twoTranslateWeilMatrix zetaZeroConfig k (2 * a)).PosSemidef := by
  obtain ⟨k, a, hk, hkc, heven, hreal, hp, hn, ha, hgt, _hneg⟩ :=
    exists_realEven_poleKilled_twoTranslate_negativeWitness_of_offLine_zero ρ₀ hoff
  exact ⟨k, a, hk, hkc, heven, hreal, hp, hn, ha,
    twoTranslateWeilMatrix_not_posSemidef_of_diagonal_norm_lt
      zetaZeroConfig k (2 * a) hgt⟩

#print axioms Zeta23.ExceptionalZero.twoTranslatePhaseWitness_value
#print axioms Zeta23.ExceptionalZero.not_subexponential_weilRelativeCorrelation_of_right_zero
#print axioms Zeta23.ExceptionalZero.exists_rightHalf_reflection_of_offLine
#print axioms Zeta23.ExceptionalZero.exists_realEven_poleKilled_twoTranslate_negativeWitness_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_realEven_poleKilled_twoTranslate_not_posSemidef_of_offLine_zero

end Zeta23.ExceptionalZero
