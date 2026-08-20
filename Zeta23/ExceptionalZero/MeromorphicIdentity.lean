import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Order

noncomputable section

namespace Zeta23.ExceptionalZero

open Set Filter Topology

/-- Meromorphic identity propagation on a preconnected domain.  Because meromorphic functions may
be assigned arbitrary values at their poles, the conclusion is intentionally punctured-local:
agreement on one genuine neighborhood forces agreement in a punctured neighborhood of every point
of the domain. -/
theorem meromorphic_eventuallyEq_nhdsNE_of_isPreconnected
    {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsPreconnected U) {x : ℂ} (hx : x ∈ U)
    (hseed : f =ᶠ[𝓝 x] g) :
    ∀ y ∈ U, f =ᶠ[𝓝[≠] y] g := by
  have hdiff : MeromorphicOn (f - g) U := hf.sub hg
  have hxzero : (f - g) =ᶠ[𝓝[≠] x] 0 := by
    filter_upwards [hseed.filter_mono nhdsWithin_le_nhds] with z hz
    simp [hz]
  have hxord : meromorphicOrderAt (f - g) x = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr hxzero
  intro y hy
  have hyord : meromorphicOrderAt (f - g) y = ⊤ := by
    by_contra hyfinite
    have hxfinite := hdiff.meromorphicOrderAt_ne_top_of_isPreconnected
      (x := y) (y := x) hU hy hx hyfinite
    exact hxfinite hxord
  have hyzero : (f - g) =ᶠ[𝓝[≠] y] 0 :=
    meromorphicOrderAt_eq_top_iff.mp hyord
  filter_upwards [hyzero] with z hz
  exact sub_eq_zero.mp (by simpa only [Pi.sub_apply] using hz)

end Zeta23.ExceptionalZero
