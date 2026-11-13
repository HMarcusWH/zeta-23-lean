import Zeta23.OPICARound4.ActualSourceHyperbola
import Zeta23.OPICARound4.ArithmeticFrontier.GrowthClosure

/-!
# Contract (C2) with coarse growth: subexponential lower bounds on the literal long term

The existing consumer `riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower`
takes an eventual constant lower bound on the literal long term
`T(t) = hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)`.
This module weakens the premise:

* a fixed-rate bound `T(t) ≥ -C e^{α t}` for all late `t`, with `α ≥ 0`, excludes
  every zero with displacement greater than `α`;
* (C2-SE) such a bound for every positive rate, and in particular a polynomial
  bound `T(t) ≥ -C (1 + t)^d`, implies Mathlib's `RiemannHypothesis`.

The time variable is `t = 2a`: a rate `α` in `t` is a rate `2α` in the correlation
separation `a`, and it is compared with the actual signed excursion
`F(a) < -M e^{2βa}` for `β < δ`. The explicit formula, the bounded archimedean
term, the vanishing reflected history and the rapid short-term error are the
existing public theorems; nothing is dropped. Coverage is every sufficiently late
time; a favorable subsequence does not suffice. The premises are OPEN.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM ExceptionalZero Filter

/-- A fixed-rate lower bound on the literal long term at every late time. -/
def ActualLongTermFixedRateLowerBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
    -(C * Real.exp (α * t)) ≤
      hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)

/-- **Contract (C2-SE).** Every positive rate, every late time. OPEN. -/
def ActualLongTermSubexponentialLowerBound : Prop :=
  ∀ α : ℝ, 0 < α → ActualLongTermFixedRateLowerBound α

/-- The polynomial specialization of (C2-SE). OPEN. -/
def ActualLongTermPolynomialLowerBound : Prop :=
  ∃ (C : ℝ) (d : ℕ) (T : ℝ), 0 < C ∧ ∀ t : ℝ, T ≤ t →
    -(C * (1 + t) ^ d) ≤
      hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)

/-- A long-term bound of rate `α ≥ 0` in `t = 2a` gives a lower bound of rate `2α`
on the literal correlation in `a`, with every source term retained. -/
theorem correlation_lower_of_longTerm_fixed_rate {α : ℝ} (hα : 0 ≤ α)
    (h : ActualLongTermFixedRateLowerBound α) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ a : ℝ, A ≤ a →
      -(K * Real.exp (2 * α * a)) ≤ fixedOriginalSincCorrelationReal a := by
  obtain ⟨C, hC, T, hT⟩ := h
  obtain ⟨D, hD, S, hS, hsmall⟩ := actualCorrelationPrimeField_add_longTerm_rapid_bound 1 (by norm_num)
  obtain ⟨B, hB, harch⟩ := actualCorrelationArch_uniform_bound
  refine ⟨B + D + C, max (max T S) (2 * UniversalSinc.fixedScale + 1) / 2, by linarith, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ 2 * UniversalSinc.fixedScale + 1 := by
      linarith [UniversalSinc.fixedScale_pos]
    have := h0.trans (le_max_right (max T S) _)
    linarith
  · intro a ha
    have ha2 : max (max T S) (2 * UniversalSinc.fixedScale + 1) ≤ 2 * a := by linarith
    have ht := (le_max_left T S).trans ((le_max_left (max T S) _).trans ha2)
    have hs := (le_max_right T S).trans ((le_max_left (max T S) _).trans ha2)
    have hpos : 0 ≤ 2 * a := hS.trans hs
    have he : Real.exp (-(1 : ℝ) * (2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he' := mul_le_mul_of_nonneg_left he hD.le
    have hp := (abs_le.mp (hsmall (2 * a) hs)).2
    have hb := hT (2 * a) ht
    have ha' : 2 * UniversalSinc.fixedScale < 2 * a := by
      have hx := (le_max_right (max T S) _).trans ha2
      linarith
    have hrate : Real.exp (α * (2 * a)) = Real.exp (2 * α * a) := by ring_nf
    rw [hrate] at hb
    have hone : 1 ≤ Real.exp (2 * α * a) := Real.one_le_exp (by nlinarith)
    rw [actualCorrelation_explicit_formula, actualCorrelationPrimeField_reflected_zero (2 * a) ha']
    have har := (abs_le.mp (harch (2 * a))).1
    nlinarith

/-- **Fixed-rate exclusion for (C2).** A long-term bound of rate `α ≥ 0` at every
late time excludes every zero with displacement greater than `α`. -/
theorem abs_re_sub_half_le_of_longTerm_fixed_rate {α : ℝ} (hα : 0 ≤ α)
    (h : ActualLongTermFixedRateLowerBound α) (ρ : zetaZeroConfig.carrier) :
    |(ρ : ℂ).re - 1 / 2| ≤ α := by
  by_contra hgt
  replace hgt := not_le.mp hgt
  obtain ⟨K, A, hK, hA, hlow⟩ := correlation_lower_of_longTerm_fixed_rate hα h
  have hoff : (ρ : ℂ).re ≠ 1 / 2 := by
    intro heq
    rw [heq, sub_self, abs_zero] at hgt
    linarith
  set δ := |(ρ : ℂ).re - 1 / 2| with hδ
  have hβδ : (α + δ) / 2 < δ := by linarith
  have hαβ : α ≤ (α + δ) / 2 := by linarith
  obtain ⟨a, haA, hval⟩ :=
    (fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero ρ hoff hβδ A (K + 1)).2
  have hlo := hlow a haA.le
  have ha0 : 0 ≤ a := hA.trans haA.le
  have hmono : Real.exp (2 * α * a) ≤ Real.exp (2 * ((α + δ) / 2) * a) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hepos : 0 < Real.exp (2 * ((α + δ) / 2) * a) := Real.exp_pos _
  nlinarith

/-- (C2-SE) excludes every off-line zero. -/
theorem no_off_line_zero_of_longTerm_subexponential
    (h : ActualLongTermSubexponentialLowerBound) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  have hle : ∀ α : ℝ, 0 < α → |(ρ : ℂ).re - 1 / 2| ≤ α :=
    fun α hα => abs_re_sub_half_le_of_longTerm_fixed_rate hα.le (h α hα) ρ
  have h0 : |(ρ : ℂ).re - 1 / 2| ≤ 0 := by
    by_contra hpos
    replace hpos := not_le.mp hpos
    have := hle (|(ρ : ℂ).re - 1 / 2| / 2) (by linarith)
    linarith
  have := abs_nonpos_iff.mp h0
  linarith

/-- **Conditional reduction (C2-SE) → RH.** The arithmetic premise remains OPEN. -/
theorem riemannHypothesis_of_longTerm_subexponential
    (h : ActualLongTermSubexponentialLowerBound) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hm : s ∈ zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  exact no_off_line_zero_of_longTerm_subexponential h ⟨s, hm⟩

/-- A polynomial long-term bound implies (C2-SE) by explicit domination. -/
theorem longTerm_subexponential_of_polynomial (h : ActualLongTermPolynomialLowerBound) :
    ActualLongTermSubexponentialLowerBound := by
  obtain ⟨C, d, T, hC, hb⟩ := h
  intro α hα
  refine ⟨C * (d.factorial * Real.exp α / α ^ d), ?_, max T 0, ?_⟩
  · have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
    positivity
  · intro t ht
    have hT : T ≤ t := le_trans (le_max_left _ _) ht
    have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    have hdom := one_add_pow_le_mul_exp hα d (show -1 ≤ t by linarith)
    have hmul := mul_le_mul_of_nonneg_left hdom hC.le
    have hbt := hb t hT
    nlinarith

/-- **Conditional reduction (C2 polynomial) → RH.** OPEN premise. -/
theorem riemannHypothesis_of_longTerm_polynomial (h : ActualLongTermPolynomialLowerBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_longTerm_subexponential (longTerm_subexponential_of_polynomial h)

/-- The existing constant-floor premise is the rate-zero case of the fixed-rate
bound; the two consumers agree on it. -/
theorem longTerm_fixed_rate_zero_of_constant
    (h : ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      -C ≤ hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)) :
    ActualLongTermFixedRateLowerBound 0 := by
  obtain ⟨C, hC, T, hT⟩ := h
  refine ⟨C, hC, T, fun t ht => ?_⟩
  simpa only [zero_mul, Real.exp_zero, mul_one] using hT t ht

end Zeta23.OPICARound4.ArithmeticFrontier
