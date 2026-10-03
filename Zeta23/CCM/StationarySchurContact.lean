import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Zeta23.CCM.CanonicalCompressedApertureC2

noncomputable section

namespace Zeta23.CCM

open Set Filter

/-!
# Post-#282 stationary contact necessity

The scalar theorem below is the sign core of the finite-dimensional Schur
argument.  It is deliberately independent of zeta/CCM source semantics.
-/

/-- A C2 scalar first-contact profile that is nonnegative to the left,
arbitrarily negative to the right, and stationary has zero second derivative. -/
theorem stationary_firstContact_secondDerivative_eq_zero
    {f : ℝ → ℝ} {x a b : ℝ}
    (hax : a < x)
    (hxb : x < b)
    (hzero : f x = 0)
    (hleft : ∀ y, a ≤ y → y ≤ x → 0 ≤ f y)
    (hright : ∀ ε > 0, ∃ y, x < y ∧ y < x + ε ∧ f y < 0)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hstat : deriv f x = 0) :
    deriv (deriv f) x = 0 := by
  have hfirst : HasDerivAt f 0 x := by
    simpa [hstat] using hC2.differentiableAt.hasDerivAt
  have hsecond :
      HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    exact hC2.deriv_contDiffAt.differentiableAt.hasDerivAt
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hderivPosLeft :
        ∀ᶠ y in 𝓝[<] x, 0 < deriv f y := by
      have hlim := hsecond.isLittleO
      filter_upwards [hlim.eventually] with y hy
      have hx : y - x < 0 := by
        simpa [mem_Iio] using show y ∈ Iio x from by assumption
      nlinarith [norm_nonneg (deriv f y - deriv f x -
        (deriv (deriv f) x) * (y - x))]
    obtain ⟨y, hyax, hyx, hdy⟩ :
        ∃ y, a < y ∧ y < x ∧ 0 < deriv f y := by
      rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
        hderivPosLeft).1 with ⟨s, hs, hsx⟩
      obtain ⟨y, hy⟩ := exists_mem_open_interval_of_mem_nhds hs hax
      exact ⟨y, hy.1, hy.2, hsx hy.2⟩
    have hmv :=
      exists_ratio_hasDerivAt_eq_slope f
        (min y x) (max y x)
        (by linarith)
        (fun z hz => hC2.continuousAt.continuousWithinAt)
        (fun z hz => hC2.differentiableAt.hasDerivAt)
    linarith [hleft y (le_of_lt hyax) (le_of_lt hyx)]
  · have hlocalPos : ∀ᶠ y in 𝓝[>] x, 0 < f y := by
      have hquad := hC2.isLittleO_sub_first
      filter_upwards [hquad.eventually] with y hy
      have hyx : 0 < y - x := by
        simpa [mem_Ioi] using show y ∈ Ioi x from by assumption
      nlinarith
    obtain ⟨ε, hε, hball⟩ := eventually_nhdsWithin_iff.1 hlocalPos
    obtain ⟨y, hyx, hyu, hyneg⟩ := hright ε hε
    have hypos : 0 < f y := hball ⟨by linarith, hyx⟩
    linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.stationary_firstContact_secondDerivative_eq_zero
