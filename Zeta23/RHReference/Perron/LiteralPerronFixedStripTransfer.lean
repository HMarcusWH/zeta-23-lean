import Zeta23.RHReference.Perron.LiteralPerronFixedGapBound
import Zeta23.RHReference.Perron.PerronFixedGapEdges

/-!
The literal-ramp Perron transfer from one fixed zero-free threshold.
The evaluation line must lie strictly to the right of that threshold.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter

namespace Zeta23.RHReference

/-- Given one zero-free half-plane, bound the actual centered native ramp
on every x ≥ 2 at any fixed exponent strictly inside that half-plane. -/
theorem abs_native_literalG_le_of_fixedGap {β σ : ℝ}
    (hβ : 1 / 2 ≤ β) (hβσ : β < σ) (hσ1 : σ < 1)
    (hzero : ∀ s : ℂ, β < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ≥ 2,
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x| ≤ A * x ^ σ := by
  obtain ⟨C, hC, hLog⟩ :=
    riemannZeta_fixedGap_vertical_logDerivative_bound hβ hβσ hσ1 hzero le_rfl hσ1.ne
  have hβ0 : 0 ≤ β := by linarith
  apply fixedGap_native_literalG_power_bound (C := C) hβ0 hβσ hσ1 hC.le hzero
  · intro t
    simpa [perronPoint, neg_div, norm_neg, Real.norm_eq_abs] using hLog t
  · intro x hx
    exact (literalPerron_horizontal_decay_of_fixedGap (by linarith) hβ hβσ hσ1 hzero).1
  · intro x hx
    exact (literalPerron_horizontal_decay_of_fixedGap (by linarith) hβ hβσ hσ1 hzero).2

/-- One fixed zero-free threshold supplies the eventual one-sided native
ramp estimate needed by the energy comparison. -/
theorem fixedGap_native_literalG_eventual_upper {β σ : ℝ}
    (hβ : 1 / 2 ≤ β) (hβσ : β < σ) (hσ1 : σ < 1)
    (hzero : ∀ s : ℂ, β < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop,
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x ≤ A * x ^ σ := by
  obtain ⟨A, hA, hbound⟩ := abs_native_literalG_le_of_fixedGap hβ hβσ hσ1 hzero
  refine ⟨A, hA, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact (le_abs_self _).trans (hbound x hx)

/-- Fixed one-tolerance input in the normalization of the energy adapter. -/
theorem literalRamp_fixed_gap_transfer {t : ℝ} (ht : 0 < t) (ht1 : t < 1 / 2)
    (hzero : ∀ s : ℂ, 1 / 2 + t / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop,
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1)) -
        x * Real.log x + (1 + Real.eulerMascheroniConstant) * x ≤ A * x ^ (1 / 2 + t) :=
  fixedGap_native_literalG_eventual_upper (β := 1 / 2 + t / 2) (σ := 1 / 2 + t)
    (by linarith) (by linarith) (by linarith) hzero

#print axioms Zeta23.RHReference.abs_native_literalG_le_of_fixedGap
#print axioms Zeta23.RHReference.fixedGap_native_literalG_eventual_upper
#print axioms Zeta23.RHReference.literalRamp_fixed_gap_transfer

end Zeta23.RHReference
