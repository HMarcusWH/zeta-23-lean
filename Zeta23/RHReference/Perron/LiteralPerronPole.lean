import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The first two coefficients of the regularized literal-ramp Perron integrand
at the pole of zeta. The first derivative is exactly the native centering
term. The rectangle contour and global vertical bounds are separate.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped Topology

namespace Zeta23.RHReference

def literalPerronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s / (s * (s - 1))

def literalPerronRegularAtOne (x : ℝ) (s : ℂ) : ℂ :=
  ((x : ℂ) ^ s / s) * (1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s))

theorem literalPerronRegularAtOne_value (x : ℝ) :
    literalPerronRegularAtOne x 1 = (x : ℂ) := by
  simp [literalPerronRegularAtOne]

theorem literalPerronRegularAtOne_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (literalPerronRegularAtOne x)
      (↑(x * Real.log x - (1 + Real.eulerMascheroniConstant) * x) : ℂ) 1 := by
  have hpow : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s)
      ((x : ℂ) * Complex.log (x : ℂ)) 1 := by
    simpa using
      (hasStrictDerivAt_const_cpow (x := (x : ℂ)) (y := (1 : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.2 hx.ne'))).hasDerivAt
  have hweight := hpow.div (hasDerivAt_id (1 : ℂ)) (by simp)
  have hz : DifferentiableAt ℂ (fun s => deriv riemannZeta₁ s / riemannZeta₁ s) 1 :=
    differentiable_riemannZeta₁.deriv.differentiableAt.div
      differentiable_riemannZeta₁.differentiableAt (by simp)
  have hfactor := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
    (((hasDerivAt_id (1 : ℂ)).sub_const 1).mul hz.hasDerivAt)
  convert hweight.mul hfactor using 1 <;> try rfl
  all_goals try simp [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    ← Complex.ofReal_log hx.le]
  all_goals try ring

theorem literalPerronRegularAtOne_eventuallyEq (x : ℝ) :
    (fun s : ℂ => (s - 1)^2 * literalPerronIntegrand x s)
      =ᶠ[𝓝[≠] (1 : ℂ)] literalPerronRegularAtOne x := by
  have hnot0' : ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), s ≠ 0 :=
    compl_singleton_mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0)
  have hnot0 := hnot0'.filter_mono
    (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
  filter_upwards [eventually_mem_nhdsWithin, hnot0,
    log_deriv_riemannZeta_eq_neg_inv_sub_add] with s hs hs0 hlog
  have hs1 : s ≠ 1 := hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold literalPerronIntegrand literalPerronRegularAtOne
  rw [neg_div, hlog]
  field_simp
  <;> ring

#print axioms Zeta23.RHReference.literalPerronRegularAtOne_value
#print axioms Zeta23.RHReference.literalPerronRegularAtOne_deriv
#print axioms Zeta23.RHReference.literalPerronRegularAtOne_eventuallyEq

end Zeta23.RHReference
