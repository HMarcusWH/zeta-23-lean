import Zeta23.CCM.CanonicalLocalBirdfishie
import Mathlib.Analysis.Convex.Deriv

noncomputable section

namespace Zeta23.CCM

open Set Filter Topology

/-!
# WP1: reciprocal-aperture calculus

For twice-differentiable scalar energy E, G(s)=E(1/s) satisfies
G''(s) = (1/s)^4 (E''(1/s) + 2 s E'(1/s)).
A curvature sign must be independently established before this yields
concavity. It is not a global all-aperture positivity theorem.
-/

/-- Derivative of the reciprocal pullback on the positive half-line. -/
theorem reciprocalAperture_first_derivative
    (f : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hf : DifferentiableAt ℝ f s⁻¹) :
    deriv (fun t : ℝ => f t⁻¹) s =
      deriv f s⁻¹ * (-(s⁻¹)^2) := by
  have hInv : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv (ne_of_gt hs)
  have h : HasDerivAt (fun t : ℝ => f t⁻¹)
      (deriv f s⁻¹ * (-(s ^ 2)⁻¹)) s := by
    simpa only [Function.comp_def] using hf.hasDerivAt.comp s hInv
  simpa only [inv_pow] using h.deriv

/-- The exact reciprocal-aperture second-derivative chain rule. -/
theorem reciprocalAperture_second_derivative
    (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf2 : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    (s : ℝ) (hs : 0 < s) :
    deriv (deriv (fun t : ℝ => f t⁻¹)) s =
      (s⁻¹)^4 * (deriv (deriv f) s⁻¹ + 2 * s * deriv f s⁻¹) := by
  have hInv : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv (ne_of_gt hs)
  have hComposed : HasDerivAt (fun t : ℝ => deriv f t⁻¹)
      (deriv (deriv f) s⁻¹ * (-(s ^ 2)⁻¹)) s := by
    simpa only [Function.comp_def] using
      ((hf2 s⁻¹ (inv_pos.mpr hs)).hasDerivAt.comp s hInv)
  have hInvSquared : HasDerivAt (fun t : ℝ => -(t⁻¹)^2)
      (-(2 * (s⁻¹) * (-(s ^ 2)⁻¹))) s := (hInv.pow 2).neg
  have hMain := hComposed.mul hInvSquared
  have hEq : (deriv (fun t : ℝ => f t⁻¹)) =ᶠ[𝓝 s]
      (fun t : ℝ => deriv f t⁻¹ * (-(t⁻¹)^2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact reciprocalAperture_first_derivative f t ht (hf t⁻¹ (inv_pos.mpr ht))
  have hDerivative := (hMain.congr_of_eventuallyEq hEq).deriv
  rw [hDerivative]
  have hne : s ≠ 0 := ne_of_gt hs
  field_simp [ne_of_gt hs] <;> ring

/-- Euler-corrected form, with physical aperture L=1/s. -/
theorem reciprocalAperture_euler_chain
    (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf2 : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    (s : ℝ) (hs : 0 < s) :
    deriv (deriv (fun t : ℝ => f t⁻¹)) s =
      (s⁻¹)^4 * (deriv (deriv f) s⁻¹ +
        2 * deriv f s⁻¹ / (s⁻¹)) := by
  rw [reciprocalAperture_second_derivative f hf hf2 s hs]
  have hne : s ≠ 0 := ne_of_gt hs
  field_simp [ne_of_gt hs] <;> ring

end Zeta23.CCM

#print axioms Zeta23.CCM.reciprocalAperture_first_derivative
#print axioms Zeta23.CCM.reciprocalAperture_second_derivative
#print axioms Zeta23.CCM.reciprocalAperture_euler_chain
