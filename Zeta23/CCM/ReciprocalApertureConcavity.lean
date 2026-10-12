import Zeta23.CCM.CanonicalLocalBirdfishie
import Mathlib.Analysis.Convex.Deriv

noncomputable section

namespace Zeta23.CCM

open Set Filter Topology

/-!
# WP1: reciprocal-aperture calculus

For the fixed-vector energy `E`, define `G(s) = E(1/s)`.  The exact identity

  `G''(s) = (1/s)^4 * (E''(1/s) + 2 s E'(1/s))`

transports the *already established* M66 prime-free Euler-curvature sign
to reciprocal-aperture concavity.  This adds no sign beyond the M66 radius,
does not assume or prove RH, and says nothing about a moving eigenvector.
-/

/-- First reciprocal derivative, with the necessary aperture domain explicit. -/
theorem reciprocalAperture_first_derivative
    (f : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hf : DifferentiableAt ℝ f s⁻¹) :
    deriv (fun t : ℝ => f t⁻¹) s =
      deriv f s⁻¹ * (-(s⁻¹)^2) := by
  have hInv : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv (ne_of_gt hs)
  have h := hf.hasDerivAt.comp s hInv
  rw [h.deriv]
  simp only [inv_pow]

/-- The second reciprocal derivative, using differentiability of both `f`
and its ordinary derivative throughout the positive aperture domain. -/
theorem reciprocalAperture_second_derivative
    (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf2 : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    (s : ℝ) (hs : 0 < s) :
    deriv (deriv (fun t : ℝ => f t⁻¹)) s =
      (s⁻¹)^4 * (deriv (deriv f) s⁻¹ + 2 * s * deriv f s⁻¹) := by
  have hInv : HasDerivAt (fun t : ℝ => t⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv (ne_of_gt hs)
  have hMain : HasDerivAt
      (fun t : ℝ => (deriv f t⁻¹) * (-(t⁻¹)^2))
      (deriv (deriv f) s⁻¹ * (-(s ^ 2)⁻¹) * (-(s⁻¹)^2) +
        deriv f s⁻¹ * (-(2 * (s⁻¹) * (-(s ^ 2)⁻¹)))) s := by
    convert (((hf2 s⁻¹ (inv_pos.mpr hs)).hasDerivAt.comp s hInv).mul
      ((hInv.pow 2).neg)) using 1 <;> ring
  have hEq : (deriv (fun t : ℝ => f t⁻¹)) =ᶠ[𝓝 s]
      (fun t : ℝ => deriv f t⁻¹ * (-(t⁻¹)^2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact reciprocalAperture_first_derivative f t ht (hf t⁻¹ (inv_pos.mpr ht))
  have hDerivative := (hMain.congr_of_eventuallyEq hEq.symm).deriv
  rw [hDerivative]
  have hne : s ≠ 0 := ne_of_gt hs
  field_simp
  ring

/-- Euler form of the reciprocal chain rule, with `L=s⁻¹`.
Neither the sign nor positivity at endpoints is built into this identity. -/
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
  field_simp
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.reciprocalAperture_first_derivative
#print axioms Zeta23.CCM.reciprocalAperture_second_derivative
#print axioms Zeta23.CCM.reciprocalAperture_euler_chain
