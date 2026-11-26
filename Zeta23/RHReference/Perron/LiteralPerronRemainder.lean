import Zeta23.RHReference.Perron.LiteralPerronPole
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
The exact local Perron Laurent subtraction. A second-order vanishing
criterion produces an analytic remainder after the two Laurent terms are
removed, without any case split on the value of the residue.
-/

set_option autoImplicit false

noncomputable section

open Asymptotics Complex Filter
open scoped Topology

namespace Zeta23.RHReference

/-- The analytic remainder after the constant and linear Taylor coefficients. -/
theorem exists_analytic_quadratic_remainder {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ s in 𝓝 z, f s - f z - deriv f z * (s - z) = (s - z)^2 * g s := by
  let k : ℂ → ℂ := fun s => f s - f z - deriv f z * (s - z)
  have hlin : AnalyticAt ℂ (fun s : ℂ => deriv f z * (s - z)) z :=
    analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  have hk : AnalyticAt ℂ k z := (hf.sub analyticAt_const).sub hlin
  have hkValue : k z = 0 := by simp [k]
  have hkDeriv : deriv k z = 0 := by
    have hd :=
      (hf.differentiableAt.hasDerivAt.sub_const (f z)).sub
        (((hasDerivAt_id z).sub_const z).const_mul (deriv f z))
    simpa [k, Pi.sub_def] using hd.deriv
  have horder : (2 : ℕ) ≤ analyticOrderAt k z := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hk).2
    intro i hi
    interval_cases i
    · simpa only [iteratedDeriv_zero] using hkValue
    · simpa only [iteratedDeriv_one] using hkDeriv
  obtain ⟨g, hga, hfg⟩ := (natCast_le_analyticOrderAt hk).1 horder
  refine ⟨g, hga, ?_⟩
  simpa only [k, smul_eq_mul] using hfg

def literalPerronResidue (x : ℝ) : ℂ :=
  ↑(x * Real.log x - (1 + Real.eulerMascheroniConstant) * x)

def literalPerronDoubleTerm (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) / (s - 1)^2

theorem analyticAt_literalPerronRegularAtOne {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (literalPerronRegularAtOne x) 1 := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) 1 := by
    simp_rw [Complex.cpow_def, if_neg hx0]
    exact analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)
  have hB : AnalyticAt ℂ riemannZeta₁ 1 := differentiable_riemannZeta₁.analyticAt 1
  have hquot : AnalyticAt ℂ (fun s => deriv riemannZeta₁ s / riemannZeta₁ s) 1 :=
    hB.deriv.div hB (by simp)
  exact (hpow.div analyticAt_id (by simp)).mul
    (analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul hquot))

/-- The actual literal Perron integrand differs from its two principal
parts by an analytic germ at the zeta pole. -/
theorem literalPerron_has_analytic_remainder {x : ℝ} (hx : 0 < x) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ),
        literalPerronIntegrand x s - literalPerronDoubleTerm x s -
          literalPerronResidue x / (s - 1) = g s := by
  obtain ⟨g, hga, hg⟩ :=
    exists_analytic_quadratic_remainder (analyticAt_literalPerronRegularAtOne hx)
  refine ⟨g, hga, ?_⟩
  have hD : deriv (literalPerronRegularAtOne x) 1 = literalPerronResidue x :=
    (literalPerronRegularAtOne_deriv hx).deriv
  have hg' := hg.filter_mono (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
  filter_upwards [hg', literalPerronRegularAtOne_eventuallyEq x, eventually_mem_nhdsWithin]
    with s hrem hscaled hs
  have hw : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [literalPerronRegularAtOne_value, hD, ← hscaled] at hrem
  unfold literalPerronDoubleTerm
  apply (mul_right_cancel₀ (pow_ne_zero 2 hw))
  field_simp
  linear_combination hrem

/-- This is the local input for a simple residue theorem after subtraction
of the zero-contour-integral pure double term. -/
theorem literalPerron_sub_double_residue_bigO {x : ℝ} (hx : 0 < x) :
    (fun s : ℂ => literalPerronIntegrand x s - literalPerronDoubleTerm x s -
      literalPerronResidue x / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  obtain ⟨g, hga, hg⟩ := literalPerron_has_analytic_remainder hx
  have heq : (fun s : ℂ => literalPerronIntegrand x s - literalPerronDoubleTerm x s -
      literalPerronResidue x / (s - 1)) =ᶠ[𝓝[≠] (1 : ℂ)] g := hg
  exact (hga.continuousAt.isBigO.mono nhdsWithin_le_nhds).congr' heq.symm EventuallyEq.rfl

#print axioms Zeta23.RHReference.exists_analytic_quadratic_remainder
#print axioms Zeta23.RHReference.literalPerron_has_analytic_remainder
#print axioms Zeta23.RHReference.literalPerron_sub_double_residue_bigO

end Zeta23.RHReference
