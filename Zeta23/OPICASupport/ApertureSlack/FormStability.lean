import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
A strict whole-set quadratic lower bound survives operator-norm perturbation.
The fixed set need not be a subspace, finite-dimensional, or nontrivial.
-/
noncomputable section

open Filter
open scoped Topology

namespace Zeta23.OPICARound22.ApertureSlack

/-- A positive lower margin on any fixed set persists under a continuous
operator perturbation. This includes the zero-dimensional case. -/
theorem eventually_lower_bound_on_set_of_operator_continuity
    {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {a₀ : α} {A : α → E →L[ℂ] E}
    (hA : ContinuousAt A a₀) (S : Set E) {μ : ℝ} (hμ : 0 < μ)
    (hmargin : ∀ x ∈ S, μ * ‖x‖ ^ 2 ≤ (inner ℂ (A a₀ x) x).re) :
    ∀ᶠ a in 𝓝 a₀, ∀ x ∈ S,
      (μ / 2) * ‖x‖ ^ 2 ≤ (inner ℂ (A a x) x).re := by
  filter_upwards [hA.tendsto.eventually (eventually_norm_sub_lt (A a₀) (half_pos hμ))]
    with a ha
  intro x hx
  have hdelta : |(inner ℂ ((A a - A a₀) x) x).re| ≤
      ‖A a - A a₀‖ * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ ((A a - A a₀) x) x‖ := Complex.abs_re_le_norm _
      _ ≤ ‖(A a - A a₀) x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖A a - A a₀‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((A a - A a₀).le_opNorm x) (norm_nonneg _)
      _ = _ := by ring
  have hlo := (abs_le.mp hdelta).1
  have hsmall : ‖A a - A a₀‖ * ‖x‖ ^ 2 ≤ μ / 2 * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right ha.le (sq_nonneg _)
  have hm := hmargin x hx
  simp only [sub_apply, inner_sub_left, Complex.sub_re] at hlo
  linarith

end Zeta23.OPICARound22.ApertureSlack
