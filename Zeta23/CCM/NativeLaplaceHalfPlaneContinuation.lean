import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Tactic

/-!
# Analytic continuation on the actual punctured native Laplace domain

The exceptional point 1/2 is removed explicitly. A totalized expression
`R(w) * zeta(w+1/2)` at that point cannot replace the separate removable
pole-cancellation argument. Four intersecting convex regions establish
connectedness without any assumption about the actual transforms.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace Zeta23.CCM

def nativeLaplaceContinuationDomain : Set ℂ :=
  {w : ℂ | 0 < w.re ∧ w ≠ 1 / 2}

theorem nativeLaplaceContinuationDomain_isOpen : IsOpen nativeLaplaceContinuationDomain := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne

theorem nativeLaplaceContinuationDomain_isPreconnected :
    IsPreconnected nativeLaplaceContinuationDomain := by
  let A : Set ℂ := {w | 0 < w.re ∧ 0 < w.im}
  let B : Set ℂ := {w | 1 / 2 < w.re}
  let C : Set ℂ := {w | 0 < w.re ∧ w.im < 0}
  let D : Set ℂ := {w | 0 < w.re ∧ w.re < 1 / 2}
  have hA : IsPreconnected A :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected B := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hC : IsPreconnected C :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hD : IsPreconnected D :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt (1 / 2))).isPreconnected
  have hAB : IsPreconnected (A ∪ B) :=
    IsPreconnected.union' ⟨1 + I, by norm_num [A, B]⟩ hA hB
  have hABC : IsPreconnected ((A ∪ B) ∪ C) := by
    apply IsPreconnected.union' ?_ hAB hC
    exact ⟨1 - I, Or.inr (by norm_num [B]), by norm_num [C]⟩
  have hABCD : IsPreconnected (((A ∪ B) ∪ C) ∪ D) := by
    apply IsPreconnected.union' ?_ hABC hD
    exact ⟨(1 / 4 : ℂ) + I, Or.inl (Or.inl (by norm_num [A])), by norm_num [D]⟩
  have heq : nativeLaplaceContinuationDomain = ((A ∪ B) ∪ C) ∪ D := by
    ext w
    constructor
    · intro hw
      rcases hw with ⟨hwpos, hwne⟩
      by_cases hright : 1 / 2 < w.re
      · exact Or.inl (Or.inl (Or.inr hright))
      by_cases hu : 0 < w.im
      · exact Or.inl (Or.inl (Or.inl ⟨hwpos, hu⟩))
      by_cases hl : w.im < 0
      · exact Or.inl (Or.inr ⟨hwpos, hl⟩)
      have him : w.im = 0 := le_antisymm (le_of_not_gt hu) (le_of_not_gt hl)
      have hre : w.re ≠ 1 / 2 := by
        intro he
        apply hwne
        apply Complex.ext
        · norm_num
          exact he
        · norm_num
          exact him
      exact Or.inr ⟨hwpos, lt_of_le_of_ne (le_of_not_gt hright) hre⟩
    · intro hw
      rcases hw with ((hw | hw) | hw) | hw
      · refine ⟨hw.1, ?_⟩
        intro he
        have := hw.2
        norm_num [he] at this
      · change 1 / 2 < w.re at hw
        refine ⟨by linarith [hw], ?_⟩
        intro he
        have := hw
        norm_num [he] at this
      · refine ⟨hw.1, ?_⟩
        intro he
        have := hw.2
        norm_num [he] at this
      · refine ⟨hw.1, ?_⟩
        intro he
        have := hw.2
        norm_num [he] at this
  rw [heq]
  exact hABCD

theorem nativeLaplace_eqOn_of_eqOn_rightHalfPlane {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f nativeLaplaceContinuationDomain)
    (hg : AnalyticOnNhd ℂ g nativeLaplaceContinuationDomain)
    (hfg : ∀ w : ℂ, 1 / 2 < w.re → f w = g w) :
    EqOn f g nativeLaplaceContinuationDomain := by
  have hmem : (1 : ℂ) ∈ nativeLaplaceContinuationDomain := by
    norm_num [nativeLaplaceContinuationDomain]
  have hlocal : f =ᶠ[𝓝 (1 : ℂ)] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)] with w hw
    exact hfg w hw
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    nativeLaplaceContinuationDomain_isPreconnected hmem hlocal

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeLaplaceContinuationDomain_isPreconnected
#print axioms Zeta23.CCM.nativeLaplace_eqOn_of_eqOn_rightHalfPlane
