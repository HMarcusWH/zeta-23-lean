import Zeta23.CCM.CanonicalLocalBirdfishie
import Mathlib.Analysis.Convex.Deriv

noncomputable section

/-!
# WP1 — Reciprocal-aperture calculus

The identity below is a real-variable chain rule.  It contains no prime or
zeta sign hypothesis.  Its strict-concavity corollary is conditional on an
*independently proved* Euler-curvature inequality.  It does not imply any
global canonical positivity or exclusion of RH counterexamples.

The native instance in \`CanonicalLocalBirdfishie\` already establishes the
Euler inequality below \`primeFreeRadius K\`; future WP1/WP2 integration uses
this generic lemma without re-proving the F04 source identity.
-/

namespace Zeta23.CCM

open Set Filter Topology

/-- Second derivative under the reciprocal aperture transformation:
\`G(s)=f(1/s)\`, so \`G''(s)=L⁴ (f''(L)+2 f'(L)/L)\` for \`L=1/s\`.
The two differentiability assumptions are explicitly required on the
positive axis, avoiding the artificial zero derivative of \`deriv\` where a
function is not differentiable. -/
theorem reciprocal_aperture_second_deriv
    (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf' : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    {s : ℝ} (hs : 0 < s) :
    (deriv^[2] (fun t : ℝ => f t⁻¹)) s =
      (s⁻¹) ^ 4 *
        ((deriv^[2] f) (s⁻¹) + 2 * s * deriv f (s⁻¹)) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hfirst : ∀ t : ℝ, 0 < t →
      deriv (fun y : ℝ => f y⁻¹) t =
        -(t ^ 2)⁻¹ * deriv f (t⁻¹) := by
    intro t ht
    have hd := ((hf _ (inv_pos.mpr ht)).hasDerivAt.comp t
      (hasDerivAt_inv (ne_of_gt ht))).deriv
    convert hd using 1 <;> ring
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
    convert (hasDerivAt_id s).pow 2 using 1 <;> ring
  have hneg : HasDerivAt (fun t : ℝ => -(t ^ 2)⁻¹)
      (2 * s / (s ^ 2) ^ 2) s := by
    convert (hpow.inv (pow_ne_zero 2 hs0)).neg using 1 <;> ring
  have hcomp : HasDerivAt (fun t : ℝ => deriv f (t⁻¹))
      (deriv (deriv f) (s⁻¹) * (-(s ^ 2)⁻¹)) s :=
    ((hf' _ (inv_pos.mpr hs)).hasDerivAt).comp s (hasDerivAt_inv hs0)
  have hmul := hneg.mul hcomp
  have hevent :
      (fun t : ℝ => deriv (fun y : ℝ => f y⁻¹) t) =ᶠ[𝓝 s]
        (fun t : ℝ => -(t ^ 2)⁻¹ * deriv f (t⁻¹)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact hfirst t ht
  have hsecond : HasDerivAt
      (fun t : ℝ => deriv (fun y : ℝ => f y⁻¹) t)
      (2 * s / (s ^ 2) ^ 2 * deriv f (s⁻¹) +
        (-(s ^ 2)⁻¹) *
          (deriv (deriv f) (s⁻¹) * (-(s ^ 2)⁻¹))) s := by
    rw [Filter.EventuallyEq.hasDerivAt_iff hevent]
    convert hmul using 1 <;> ring
  simp only [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hsecond.deriv]
  field_simp [hs0]
  ring

/-- A strictly negative Euler-corrected curvature on \`(0,R)\` implies
strict concavity *in reciprocal aperture*.  The second-derivative sign
must be supplied independently; this theorem is not a contact prohibition. -/
theorem strictConcaveOn_reciprocal_of_euler_neg
    (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hf' : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (deriv f) x)
    (heuler : ∀ L ∈ Ioo (0 : ℝ) R,
        (deriv^[2] f) L + 2 * deriv f L / L < 0) :
    StrictConcaveOn ℝ (Ioi (1 / R)) (fun s : ℝ => f s⁻¹) := by
  have hdomain : ∀ s ∈ Ioi (1 / R), 0 < s ∧ s⁻¹ ∈ Ioo (0 : ℝ) R := by
    intro s hs
    have hspos : 0 < s := lt_trans (one_div_pos.mpr hR) hs
    have hmul : 1 < s * R := (div_lt_iff₀ hR).mp hs
    have hinv : s⁻¹ < R := by
      apply (div_lt_iff₀ hspos).2
      nlinarith
    exact ⟨hspos, ⟨inv_pos.mpr hspos, hinv⟩⟩
  have hcont : ContinuousOn (fun s : ℝ => f s⁻¹) (Ioi (1 / R)) := by
    intro s hs
    have hh := hdomain s hs
    exact (((hf _ hh.2.1).hasDerivAt.comp s
      (hasDerivAt_inv (ne_of_gt hh.1))).continuousAt).continuousWithinAt
  have hsecond : ∀ s ∈ Ioi (1 / R),
      (deriv^[2] (fun t : ℝ => f t⁻¹)) s < 0 := by
    intro s hs
    have hh := hdomain s hs
    rw [reciprocal_aperture_second_deriv f hf hf' hh.1]
    have hcurv : (deriv^[2] f) (s⁻¹) +
        2 * s * deriv f (s⁻¹) < 0 := by
      convert heuler (s⁻¹) hh.2 using 1 <;>
        field_simp [ne_of_gt hh.1] <;> ring
    exact mul_neg_of_pos_of_neg (pow_pos hh.2.1 4) hcurv
  exact strictConcaveOn_of_deriv2_neg' (convex_Ioi _) hcont hsecond

end Zeta23.CCM

#print axioms Zeta23.CCM.reciprocal_aperture_second_deriv
#print axioms Zeta23.CCM.strictConcaveOn_reciprocal_of_euler_neg
