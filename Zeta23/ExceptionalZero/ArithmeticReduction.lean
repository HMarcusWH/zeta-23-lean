import Zeta23.ExceptionalZero.WeilFilter

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-! ## The exact remaining blocker of route R001

`ArithmeticSideSubexponential` is the precise arithmetic upper-bound statement that route R001
still requires: for every admissible pole-killed Weil test, the literature explicit-formula RHS
of the right-translated tests is subexponential in the aperture.

Two theorems below pin down its exact logical strength:

* `criticalLine_of_arithmeticSideSubexponential` — it implies RH (via the exposed-pole detector,
  target-adaptive visibility, and the zeta reflection `ρ ↦ 1 − ρ̄`);
* `arithmeticSideSubexponential_of_criticalLine` — RH implies it (on the critical line every
  filtered mode has unit modulus, so the family is bounded).

"RH" here and below means the repository's strip-zero rendering — every nontrivial zero
(`IsNontrivialZero`: `ζρ = 0 ∧ 0 < Re ρ < 1`) has `Re ρ = 1/2` — the same form as the
comparator statements and the RHRC claim `C_RH`.

Together: the scalar-observable form of `R001_PRIME_UPPER` is **equivalent** to RH.  It is not
"one more prime estimate"; any unconditional proof of it must contain RH-strength information.
This is recorded as a theorem, not an obstruction ledger entry alone, so that no future route
iteration can silently treat this statement as an independent arithmetic target. -/

/-- The exact remaining arithmetic obligation of route R001 (scalar form): every pole-killed
admissible Weil test has subexponential translated explicit-formula RHS. -/
def ArithmeticSideSubexponential : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    paperFT k (I / 2) = 0 → paperFT k (-I / 2) = 0 →
    Subexponential
      (fun a => ‖Zeta23.EF.literatureRHS (translateRight k (2 * a))‖)

/-- The arithmetic bound excludes zeros strictly to the right of the critical line. -/
theorem re_le_half_of_arithmeticSideSubexponential
    (h : ArithmeticSideSubexponential) (ρ₀ : zetaZeroConfig.carrier) :
    (ρ₀ : ℂ).re ≤ 1 / 2 := by
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨k, hk2, hkc, hkp1, hkp2, hnot⟩ :=
    exists_poleKilled_test_not_subexponential_of_right_zero ρ₀ hgt
  exact hnot (h k hk2 hkc hkp1 hkp2)

/-- **Conditional critical-line theorem.**  If the arithmetic side of the translated pole-killed
explicit formula is subexponential for every admissible test, then every nontrivial zeta zero
lies on the critical line.  The left half of the strip is excluded through the unconditional
reflection symmetry `ρ ↦ 1 − ρ̄` of the zero configuration, exactly as the route prescribes:
the generic detector itself only ever excludes right-side zeros. -/
theorem criticalLine_of_arithmeticSideSubexponential
    (h : ArithmeticSideSubexponential) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  have h1 : ρ.re ≤ 1 / 2 :=
    re_le_half_of_arithmeticSideSubexponential h ⟨ρ, hρ⟩
  have hrefl : Zeta23.reflect ρ ∈ zetaZeroConfig.carrier :=
    zetaZeroConfig.reflect_mem ρ hρ
  have h2 : (Zeta23.reflect ρ).re ≤ 1 / 2 :=
    re_le_half_of_arithmeticSideSubexponential h ⟨Zeta23.reflect ρ, hrefl⟩
  have h3 : (Zeta23.reflect ρ).re = 1 - ρ.re := by
    simp [Zeta23.reflect]
  rw [h3] at h2
  linarith

/-- On the critical line every filtered mode has unit modulus, so the family is dominated by the
absolute coefficient mass at every aperture. -/
theorem norm_filteredZeroFamily_le_coeffMass_of_criticalLine
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (hline : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2) (a : ℝ) :
    ‖filteredZeroFamily φ c a‖ ≤
      ∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖ := by
  have hcoeff : Summable (fun ρ : zetaZeroConfig.carrier => ‖zeroFilterCoeff φ ρ‖) := hφ
  have hmod : ∀ ρ : zetaZeroConfig.carrier,
      ‖filteredZeroTerm φ c ρ a‖ = ‖zeroFilterCoeff φ ρ‖ := by
    intro ρ
    unfold filteredZeroTerm
    rw [norm_mul, Complex.norm_exp]
    have hre : (((2 : ℂ) * ((ρ : ℂ) - c)) * (a : ℂ)).re =
        2 * ((ρ : ℂ).re - c.re) * a := by
      simp [Complex.mul_re]
    rw [hre, hline ρ, hc]
    norm_num
  unfold filteredZeroFamily
  exact tsum_of_norm_bounded hcoeff.hasSum (fun ρ => (hmod ρ).le)

/-- A globally bounded profile is subexponential. -/
theorem subexponential_of_bounded {R : ScaleProfile} {M : ℝ}
    (hM : ∀ a : ℝ, 0 ≤ a → R a ≤ M) : Subexponential R := by
  intro ε hε
  refine ⟨max 0 (Real.log (max M 1) / ε), fun a ha => ?_⟩
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have haM : Real.log (max M 1) / ε ≤ a := le_trans (le_max_right _ _) ha
  have hM1 : (0 : ℝ) < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc
    R a ≤ M := hM a ha0
    _ ≤ max M 1 := le_max_left _ _
    _ = Real.exp (Real.log (max M 1)) := (Real.exp_log hM1).symm
    _ ≤ Real.exp (ε * a) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ hε] at haM
      linarith [haM]

/-- **Converse direction: RH implies the arithmetic bound.**  If every nontrivial zero lies on
the critical line, then for every admissible test the translated explicit-formula RHS equals a
filtered zero family all of whose modes have unit modulus; it is therefore bounded, hence
subexponential.  Together with `criticalLine_of_arithmeticSideSubexponential` this proves that
the scalar remaining blocker of R001 is exactly equivalent to RH — it cannot be closed by any
argument weaker than RH itself. -/
theorem arithmeticSideSubexponential_of_criticalLine
    (hRH : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) :
    ArithmeticSideSubexponential := by
  intro k hk2 hkc _ _
  have hφ := absolutelySummableZeroFilter_weil hk2 hkc
  have hc : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hline : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => hRH (ρ : ℂ) ρ.2
  have hbound : ∀ a : ℝ, 0 ≤ a →
      ‖Zeta23.EF.literatureRHS (translateRight k (2 * a))‖ ≤
        ∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff (weilZeroFilter k) ρ‖ := by
    intro a _
    rw [← filteredZeroFamily_weilZeroFilter_eq_literatureRHS hk2 hkc a]
    exact norm_filteredZeroFamily_le_coeffMass_of_criticalLine hφ hc hline a
  exact subexponential_of_bounded hbound

/-- **The terminal equivalence.**  The scalar arithmetic obligation of route R001 is neither
weaker nor stronger than RH: `R001_PRIME_UPPER` in this observable class *is* RH.  Any genuinely
new unconditional input must therefore come from a different observable (operator, multi-probe,
or quadratic-form channel), never from a sharper estimate of this same scalar family. -/
theorem arithmeticSideSubexponential_iff_criticalLine :
    ArithmeticSideSubexponential ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 :=
  ⟨criticalLine_of_arithmeticSideSubexponential,
    arithmeticSideSubexponential_of_criticalLine⟩

end Zeta23.ExceptionalZero
